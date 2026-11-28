/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Scalar extension and restriction of ideal quotient modules

Let R,S,Q be commutative rings in a common world, with maps
f:R→Q and g:S→Q. For an ideal I⊆R, extending R/I to Q
and then restricting to S gives the S-module isomorphism
Res_g(Q⊗[R,f](R/I))≅Res_g(Q/f(I)Q).
It sends q⊗[r] to [f(r)q].

A surjective ring map b:Q→P identifies Q/ker(b) with P as
a Q-module. If j:S→P equals b∘g and J=ker(b), restricting
this quotient presentation gives Res_g(Q/J)≅Res_j(P),
with forward value [q]↦b(q) and inverse b(q)↦[q].
-/

public section
noncomputable section
namespace ModuleCat
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

/-- For commutative rings R,S,Q, maps f:R→Q,g:S→Q and
I⊆R an ideal, there is an S-module isomorphism
Res_g(Q⊗[R,f](R/I))≅Res_g(Q/I.map(f)).
All ring and module carriers here have world u. -/
def extendedRestrictedQuotientIso
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (f : R →+* Q) (g : S →+* Q) (I : Ideal R) :
    (ModuleCat.extendScalars.{u,u,u} f ⋙ ModuleCat.restrictScalars.{u,u,u} g).obj
        (ModuleCat.of R (R ⧸ I)) ≅
      (ModuleCat.restrictScalars.{u,u,u} g).obj (ModuleCat.of Q (Q ⧸ I.map f)) := by
  let : Algebra R Q := f.toAlgebra
  let e : (ModuleCat.extendScalars.{u,u,u} f).obj (ModuleCat.of R (R ⧸ I)) ≅
      ModuleCat.of Q (Q ⧸ I.map f) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Q I).symm.toLinearEquiv.toModuleIso
  exact (ModuleCat.restrictScalars.{u,u,u} g).mapIso e

theorem restrictedQuotient_annihilator
    (S Q : Type u) [CommRing S] [CommRing Q] (g : S →+* Q) (J : Ideal Q) :
    Module.annihilator S ((ModuleCat.restrictScalars.{u,u,u} g).obj (ModuleCat.of Q (Q ⧸ J))) =
      J.comap g := by
  ext s
  constructor
  · intro hs
    have hOne := Module.mem_annihilator.mp hs (1 : Q ⧸ J)
    change Ideal.Quotient.mk J (g s) * 1 = 0 at hOne
    change g s ∈ J
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
      (by simpa only [mul_one] using hOne)
  · intro hs
    apply Module.mem_annihilator.mpr
    change ∀ m : Q ⧸ J, _ = 0
    intro m
    change Ideal.Quotient.mk J (g s) * m = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr hs, zero_mul]

theorem extendedRestrictedQuotient_annihilator
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (f : R →+* Q) (g : S →+* Q) (a : R →+* S)
    (ha : g.comp a = f) (hg : Function.Surjective g) (I : Ideal R) :
    Module.annihilator S
        ((ModuleCat.extendScalars.{u,u,u} f ⋙ ModuleCat.restrictScalars.{u,u,u} g).obj
          (ModuleCat.of R (R ⧸ I))) =
      I.map a ⊔ RingHom.ker g := by
  rw [(extendedRestrictedQuotientIso R S Q f g I).toLinearEquiv.annihilator_eq,
    restrictedQuotient_annihilator S Q g (I.map f), ← ha, ← Ideal.map_map]
  exact Ideal.comap_map_of_surjective g hg (I.map a)

theorem extendedRestrictedScalarModule_finite
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (f : R →+* Q) (g : S →+* Q) (hg : Function.Surjective g)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite S
      ((ModuleCat.extendScalars.{u,u,u} f ⋙ ModuleCat.restrictScalars.{u,u,u} g).obj M) := by
  let : Algebra R Q := f.toAlgebra
  let : Algebra S Q := g.toAlgebra
  let E := ModuleCat.extendScalars.{u,u,u} f
  let : Module.Finite S Q := Module.Finite.of_surjective (Algebra.linearMap S Q) hg
  let : Module.Finite Q (E.obj M) := by
    change Module.Finite Q (Q ⊗[R] M)
    infer_instance
  let : Module S (E.obj M) := Module.compHom (E.obj M) g
  let : IsScalarTower S Q (E.obj M) := ⟨fun s q x => by
    change (g s * q) • x = g s • (q • x)
    exact mul_smul _ _ _⟩
  exact Module.Finite.trans (R := S) Q (E.obj M)

/-- For f:R→Q,g:S→Q between commutative rings and an
ideal I⊆R, the restricted extension-quotient isomorphism
has pure-tensor value q⊗[r]↦[f(r)q].
The target quotient is Q/I.map(f), with S-action through g. -/
theorem extendedRestrictedQuotientIso_hom_tmul
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (f : R →+* Q) (g : S →+* Q) (I : Ideal R) (q : Q) (r : R) :
    (extendedRestrictedQuotientIso R S Q f g I).hom.hom
      (q ⊗ₜ[R,f] Ideal.Quotient.mk I r) = Ideal.Quotient.mk (I.map f) (f r * q) := by
  let : Algebra R Q := f.toAlgebra
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Q I).symm
    (q ⊗ₜ[R,f] Ideal.Quotient.mk I r) = _
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul Q I q r


/-- For commutative rings R,P and a surjective map f:R→P,
the quotient R/ker(f) is isomorphic as an R-module to P
with its scalar action restricted along f. -/
def surjectiveQuotientModuleIso
    (R P : Type u) [CommRing R] [CommRing P]
    (f : R →+* P) (hf : Function.Surjective f) :
    ModuleCat.of R (R ⧸ RingHom.ker f) ≅
      (ModuleCat.restrictScalars f).obj (ModuleCat.of P P) := by
  let : Algebra R P := f.toAlgebra
  let fa : R →ₐ[R] P := { toRingHom := f, commutes' := fun _ => rfl }
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := fa) hf).toLinearEquiv.toModuleIso

/-- For a surjective commutative-ring map f:R→P,
the forward module presentation R/ker(f)→Res_f(P)
sends [r] to f(r). -/
theorem surjectiveQuotientModuleIso_hom_mk
    (R P : Type u) [CommRing R] [CommRing P]
    (f : R →+* P) (hf : Function.Surjective f) (r : R) :
    (surjectiveQuotientModuleIso R P f hf).hom.hom (Ideal.Quotient.mk (RingHom.ker f) r) = f r := by
  let : Algebra R P := f.toAlgebra
  let fa : R →ₐ[R] P := { toRingHom := f, commutes' := fun _ => rfl }
  change Ideal.quotientKerAlgEquivOfSurjective (f := fa) hf (Ideal.Quotient.mk _ r) = f r
  exact Ideal.quotientKerAlgEquivOfSurjective_mk hf r

/-- For a surjective commutative-ring map f:R→P,
the inverse Res_f(P)→R/ker(f) sends f(r) to [r].
The value is independent of the representative modulo ker(f). -/
theorem surjectiveQuotientModuleIso_inv_map
    (R P : Type u) [CommRing R] [CommRing P]
    (f : R →+* P) (hf : Function.Surjective f) (r : R) :
    (surjectiveQuotientModuleIso R P f hf).inv.hom (f r) = Ideal.Quotient.mk (RingHom.ker f) r := by
  let : Algebra R P := f.toAlgebra
  let fa : R →ₐ[R] P := { toRingHom := f, commutes' := fun _ => rfl }
  change (Ideal.quotientKerAlgEquivOfSurjective (f := fa) hf).symm (fa r) = Ideal.Quotient.mk _ r
  exact Ideal.quotientKerAlgEquivOfSurjective_symm_apply hf r

/-- For commutative-ring maps g:S→Q,b:Q→P,j:S→P,
assume b surjective, ker(b)=J and j=b∘g.
Then Res_g(Q/J)≅Res_j(P) as S-modules.
The isomorphism preserves the two scalar actions of the triangle. -/
def restrictedQuotientIsoOfSurjective
    (S Q P : CommRingCat.{u})
    (g : S ⟶ Q) (b : Q ⟶ P) (j : S ⟶ P) (J : Ideal Q)
    (hb : Function.Surjective b.hom) (hk : RingHom.ker b.hom = J) (hj : j = g ≫ b) :
    (ModuleCat.restrictScalars g.hom).obj (ModuleCat.of Q (Q ⧸ J)) ≅
      (ModuleCat.restrictScalars j.hom).obj (ModuleCat.of P P) := by
  let eK : ModuleCat.of Q (Q ⧸ J) ≅ ModuleCat.of Q (Q ⧸ RingHom.ker b.hom) :=
    (Ideal.quotientEquivAlgOfEq Q hk.symm).toLinearEquiv.toModuleIso
  let eP := surjectiveQuotientModuleIso Q P b.hom hb
  have h : j.hom = b.hom.comp g.hom := congrArg CommRingCat.Hom.hom hj
  exact (ModuleCat.restrictScalars g.hom).mapIso (eK ≪≫ eP) ≪≫
    (ModuleCat.restrictScalarsComp'App g.hom b.hom j.hom h (ModuleCat.of P P)).symm

/-- For a commuting scalar triangle j=b∘g with b:Q→P
surjective and ker(b)=J, the S-module quotient comparison
Res_g(Q/J)→Res_j(P) sends [q] to b(q). -/
theorem restrictedQuotientIsoOfSurjective_hom_mk
    (S Q P : CommRingCat.{u})
    (g : S ⟶ Q) (b : Q ⟶ P) (j : S ⟶ P) (J : Ideal Q)
    (hb : Function.Surjective b.hom) (hk : RingHom.ker b.hom = J) (hj : j = g ≫ b) (q : Q) :
    (restrictedQuotientIsoOfSurjective S Q P g b j J hb hk hj).hom.hom
      (Ideal.Quotient.mk J q) = b q := by
  unfold restrictedQuotientIsoOfSurjective
  change ((ModuleCat.restrictScalarsComp'App g.hom b.hom j.hom
    (congrArg CommRingCat.Hom.hom hj) (ModuleCat.of P P)).inv.hom)
      ((surjectiveQuotientModuleIso Q P b.hom hb).hom.hom
        ((Ideal.quotientEquivAlgOfEq Q hk.symm) (Ideal.Quotient.mk J q))) = b q
  rw [Ideal.quotientEquivAlgOfEq_mk, surjectiveQuotientModuleIso_hom_mk]
  exact ModuleCat.restrictScalarsComp'App_inv_apply g.hom b.hom j.hom
    (congrArg CommRingCat.Hom.hom hj) (ModuleCat.of P P) (b q)

/-- For commutative rings in a scalar triangle j=b∘g,
with b surjective and ker(b)=J, the inverse restricted
quotient comparison sends b(q) to [q]∈Q/J. -/
theorem restrictedQuotientIsoOfSurjective_inv_map
    (S Q P : CommRingCat.{u})
    (g : S ⟶ Q) (b : Q ⟶ P) (j : S ⟶ P) (J : Ideal Q)
    (hb : Function.Surjective b.hom) (hk : RingHom.ker b.hom = J) (hj : j = g ≫ b) (q : Q) :
    (restrictedQuotientIsoOfSurjective S Q P g b j J hb hk hj).inv.hom (b q) =
      Ideal.Quotient.mk J q := by
  let e := restrictedQuotientIsoOfSurjective S Q P g b j J hb hk hj
  let x : (ModuleCat.restrictScalars g.hom).obj (ModuleCat.of Q (Q ⧸ J)) := Ideal.Quotient.mk J q
  let y : (ModuleCat.restrictScalars j.hom).obj (ModuleCat.of P P) := b q
  have h : e.toLinearEquiv x = y :=
    restrictedQuotientIsoOfSurjective_hom_mk S Q P g b j J hb hk hj q
  have hc : e.toLinearEquiv.symm y = x := by
    rw [← h]
    exact e.toLinearEquiv.symm_apply_apply x
  exact hc

end ModuleCat
