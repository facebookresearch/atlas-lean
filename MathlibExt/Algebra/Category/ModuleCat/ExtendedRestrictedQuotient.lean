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
-/

public section
noncomputable section
namespace ModuleCat
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

/-- The actual extended quotient, with the original restricted scalar action. -/
def extendedRestrictedQuotientIso
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (f : R →+* Q) (g : S →+* Q) (I : Ideal R) :
    (ModuleCat.extendScalars.{u,u,u} f ⋙ ModuleCat.restrictScalars.{u,u,u} g).obj (ModuleCat.of R (R ⧸ I)) ≅
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
        ((ModuleCat.extendScalars.{u,u,u} f ⋙ ModuleCat.restrictScalars.{u,u,u} g).obj (ModuleCat.of R (R ⧸ I))) =
      I.map a ⊔ RingHom.ker g := by
  rw [(extendedRestrictedQuotientIso R S Q f g I).toLinearEquiv.annihilator_eq,
    restrictedQuotient_annihilator S Q g (I.map f), ← ha, ← Ideal.map_map]
  exact Ideal.comap_map_of_surjective g hg (I.map a)

theorem extendedRestrictedScalarModule_finite
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (f : R →+* Q) (g : S →+* Q) (hg : Function.Surjective g)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.extendScalars.{u,u,u} f ⋙ ModuleCat.restrictScalars.{u,u,u} g).obj M) := by
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

/-- The inherited quotient comparison retains the literal tensor and scalar values. -/
theorem extendedRestrictedQuotientIso_hom_tmul
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (f : R →+* Q) (g : S →+* Q) (I : Ideal R) (q : Q) (r : R) :
    (extendedRestrictedQuotientIso R S Q f g I).hom.hom
      (q ⊗ₜ[R,f] Ideal.Quotient.mk I r) = Ideal.Quotient.mk (I.map f) (f r * q) := by
  let : Algebra R Q := f.toAlgebra
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Q I).symm
    (q ⊗ₜ[R,f] Ideal.Quotient.mk I r) = _
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul Q I q r


/-- A surjective scalar map presents the actual target as its source-kernel quotient module. -/
def surjectiveQuotientModuleIso
    (R P : Type u) [CommRing R] [CommRing P]
    (f : R →+* P) (hf : Function.Surjective f) :
    ModuleCat.of R (R ⧸ RingHom.ker f) ≅
      (ModuleCat.restrictScalars f).obj (ModuleCat.of P P) := by
  let : Algebra R P := f.toAlgebra
  let fa : R →ₐ[R] P := { toRingHom := f, commutes' := fun _ => rfl }
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := fa) hf).toLinearEquiv.toModuleIso

/-- The quotient presentation sends the original class of `r` to the actual scalar-map value. -/
theorem surjectiveQuotientModuleIso_hom_mk
    (R P : Type u) [CommRing R] [CommRing P]
    (f : R →+* P) (hf : Function.Surjective f) (r : R) :
    (surjectiveQuotientModuleIso R P f hf).hom.hom (Ideal.Quotient.mk (RingHom.ker f) r) = f r := by
  let : Algebra R P := f.toAlgebra
  let fa : R →ₐ[R] P := { toRingHom := f, commutes' := fun _ => rfl }
  change Ideal.quotientKerAlgEquivOfSurjective (f := fa) hf (Ideal.Quotient.mk _ r) = f r
  exact Ideal.quotientKerAlgEquivOfSurjective_mk hf r

/-- The inverse quotient presentation sends an actual scalar image back to its original class. -/
theorem surjectiveQuotientModuleIso_inv_map
    (R P : Type u) [CommRing R] [CommRing P]
    (f : R →+* P) (hf : Function.Surjective f) (r : R) :
    (surjectiveQuotientModuleIso R P f hf).inv.hom (f r) = Ideal.Quotient.mk (RingHom.ker f) r := by
  let : Algebra R P := f.toAlgebra
  let fa : R →ₐ[R] P := { toRingHom := f, commutes' := fun _ => rfl }
  change (Ideal.quotientKerAlgEquivOfSurjective (f := fa) hf).symm (fa r) = Ideal.Quotient.mk _ r
  exact Ideal.quotientKerAlgEquivOfSurjective_symm_apply hf r

/-- Restriction along an actual scalar triangle preserves the quotient presentation of its target. -/
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

/-- The restricted quotient comparison retains the original target scalar value on every representative. -/
theorem restrictedQuotientIsoOfSurjective_hom_mk
    (S Q P : CommRingCat.{u})
    (g : S ⟶ Q) (b : Q ⟶ P) (j : S ⟶ P) (J : Ideal Q)
    (hb : Function.Surjective b.hom) (hk : RingHom.ker b.hom = J) (hj : j = g ≫ b) (q : Q) :
    (restrictedQuotientIsoOfSurjective S Q P g b j J hb hk hj).hom.hom (Ideal.Quotient.mk J q) = b q := by
  unfold restrictedQuotientIsoOfSurjective
  change ((ModuleCat.restrictScalarsComp'App g.hom b.hom j.hom
    (congrArg CommRingCat.Hom.hom hj) (ModuleCat.of P P)).inv.hom)
      ((surjectiveQuotientModuleIso Q P b.hom hb).hom.hom
        ((Ideal.quotientEquivAlgOfEq Q hk.symm) (Ideal.Quotient.mk J q))) = b q
  rw [Ideal.quotientEquivAlgOfEq_mk, surjectiveQuotientModuleIso_hom_mk]
  exact ModuleCat.restrictScalarsComp'App_inv_apply g.hom b.hom j.hom
    (congrArg CommRingCat.Hom.hom hj) (ModuleCat.of P P) (b q)

/-- The inverse restricted quotient comparison takes every actual scalar image to its original class. -/
theorem restrictedQuotientIsoOfSurjective_inv_map
    (S Q P : CommRingCat.{u})
    (g : S ⟶ Q) (b : Q ⟶ P) (j : S ⟶ P) (J : Ideal Q)
    (hb : Function.Surjective b.hom) (hk : RingHom.ker b.hom = J) (hj : j = g ≫ b) (q : Q) :
    (restrictedQuotientIsoOfSurjective S Q P g b j J hb hk hj).inv.hom (b q) = Ideal.Quotient.mk J q := by
  let e := restrictedQuotientIsoOfSurjective S Q P g b j J hb hk hj
  let x : (ModuleCat.restrictScalars g.hom).obj (ModuleCat.of Q (Q ⧸ J)) := Ideal.Quotient.mk J q
  let y : (ModuleCat.restrictScalars j.hom).obj (ModuleCat.of P P) := b q
  have h : e.toLinearEquiv x = y := restrictedQuotientIsoOfSurjective_hom_mk S Q P g b j J hb hk hj q
  have hc : e.toLinearEquiv.symm y = x := by
    rw [← h]
    exact e.toLinearEquiv.symm_apply_apply x
  exact hc

end ModuleCat
