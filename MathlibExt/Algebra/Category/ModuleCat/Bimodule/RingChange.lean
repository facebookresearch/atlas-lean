/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Bimodule
public import Mathlib.RingTheory.TensorProduct.Maps
public import MathlibExt.Algebra.Module.NatInt

/-!
# Endpoint restriction and semilinear maps of bimodules

Let R,S be arbitrary rings. An (R,S)-bimodule is a module over
E_(R,S)=R⊗[ℤ]Sᵒᵖ. Restricting along the two tensor inclusions gives
its left R- and right S-actions; they commute, and
(r⊗t)•x=r•(t•x). Conversely, commuting endpoint actions on an
additive commutative group define this enveloping-ring module.

For ring maps φ:R→R′ and ψ:S→S′, the enveloping map sends
r⊗t to φ(r)⊗ψᵒᵖ(t). Restriction along this map is coherent with
identity and composition and changes only the endpoint actions.

An enveloping-semilinear map is equivalent to an additive map satisfying
both endpoint equations f(r•x)=φ(r)•f(x) and
f(t•x)=ψᵒᵖ(t)•f(x). This is a bijection of Hom sets.
All endpoint-ring and coefficient carrier worlds are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe r r' r'' s s' s'' b b'

namespace ModuleCat.Bimodule.RingChange

variable {R : Type r} {S : Type s} [Ring R] [Ring S]
  {R' : Type r'} {S' : Type s'} [Ring R'] [Ring S']

/-- For ring homomorphisms φ:R→R′ and ψ:S→S′, the
enveloping map E_(R,S)→E_(R′,S′) is the tensor map
φ⊗ψᵒᵖ over ℤ. The endpoint rings may be noncommutative. -/
def envelopingRingHom (φ : R →+* R') (ψ : S →+* S') :
    R ⊗[ℤ] Sᵐᵒᵖ →+* R' ⊗[ℤ] S'ᵐᵒᵖ :=
  (Algebra.TensorProduct.map φ.toIntAlgHom ψ.op.toIntAlgHom).toRingHom

/-- For φ:R→R′, ψ:S→S′, r∈R and t∈Sᵒᵖ,
the enveloping map sends r⊗t to φ(r)⊗ψᵒᵖ(t).
The right endpoint is carried through the opposite ring map. -/
theorem envelopingRingHom_tmul (φ : R →+* R') (ψ : S →+* S')
    (r : R) (t : Sᵐᵒᵖ) :
    envelopingRingHom φ ψ (r ⊗ₜ[ℤ] t) = φ r ⊗ₜ[ℤ] ψ.op t :=
  Algebra.TensorProduct.map_tmul φ.toIntAlgHom ψ.op.toIntAlgHom r t

/-- For B∈ModuleCat(E_(R,S)), restriction along
r↦r⊗1 gives its left R-module structure.
The coefficient carrier world is independent of the two ring worlds. -/
def leftModule (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) : Module R B :=
  Module.compHom B
    (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℤ] Sᵐᵒᵖ)

/-- For B∈ModuleCat(E_(R,S)), restriction along
t↦1⊗t gives its Sᵒᵖ-module structure, hence its right
S-action on the same carrier. -/
def rightModule (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) : Module Sᵐᵒᵖ B :=
  Module.compHom B
    (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[ℤ] R ⊗[ℤ] Sᵐᵒᵖ).toRingHom

/-- For an E_(R,S)-module B, scalar restriction along
ℤ→E_(R,S) gives its integer module structure on the
underlying additive commutative group. -/
def groundModule (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) : Module ℤ B :=
  Module.compHom B (Int.castRingHom (R ⊗[ℤ] Sᵐᵒᵖ))

/-- For a module B over E_(R,S), the left R- and right
S-actions obtained from the tensor inclusions commute:
r•(t•x)=t•(r•x), r∈R and t∈Sᵒᵖ. -/
theorem commute (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) :
    letI := leftModule R S B
    letI := rightModule R S B
    SMulCommClass R Sᵐᵒᵖ B := by
  let := leftModule R S B
  let := rightModule R S B
  refine ⟨fun r t x => ?_⟩
  change (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • (((1 : R) ⊗ₜ[ℤ] t) • x) =
    ((1 : R) ⊗ₜ[ℤ] t) • ((r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • x)
  rw [← mul_smul, ← mul_smul]
  apply congrArg (fun z : R ⊗[ℤ] Sᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- For an E_(R,S)-module B, the action of r⊗t on x is
r•(t•x), using its restricted left R- and right S-actions.
This is the ordered factorization of the tensor-ring action. -/
theorem smul_tmul (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) (r : R) (t : Sᵐᵒᵖ) (x : B) :
    B.isModule.smul (r ⊗ₜ[ℤ] t) x =
      (leftModule R S B).smul r ((rightModule R S B).smul t x) := by
  change (r ⊗ₜ[ℤ] t) • x =
    (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • (((1 : R) ⊗ₜ[ℤ] t) • x)
  rw [← mul_smul]
  apply congrArg (fun z : R ⊗[ℤ] Sᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

section GivenActions

variable (R : Type r) (S : Type s) [Ring R] [Ring S] (M : Type b)
  [AddCommGroup M] [dM : Module ℤ M] [dR : Module R M] [dS : Module Sᵐᵒᵖ M]
  [SMulCommClass R Sᵐᵒᵖ M]

/-- For an additive commutative group M with specified
integer, left R- and right S-module structures, suppose the
two endpoint actions commute. Then M is a module over
E_(R,S), with (r⊗t)•x=r•(t•x). -/
def moduleOfActions : Module (R ⊗[ℤ] Sᵐᵒᵖ) M :=
  @TensorProduct.Algebra.module ℤ R Sᵐᵒᵖ M
    inferInstance (inferInstance : AddCommMonoid M) dM
    inferInstance inferInstance dR dS inferInstance inferInstance
    (Module.intModule_isScalarTower (Algebra.toModule : Module ℤ R) dM)
    (Module.intModule_isScalarTower (Algebra.toModule : Module ℤ Sᵐᵒᵖ) dM)
    inferInstance

/-- For an additive commutative group M with commuting
left R- and right S-actions and its specified ℤ-module action,
the enveloping action makes M an object of ModuleCat^b(E_(R,S)).
Its carrier is M. -/
def ofActions : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ) :=
  letI := moduleOfActions R S M
  ModuleCat.of (R ⊗[ℤ] Sᵐᵒᵖ) M

/-- For the enveloping module built from specified commuting
actions on M, restricting to the left R endpoint recovers
the given Module R M structure. -/
theorem ofActions_leftModule : leftModule R S (ofActions R S M) = dR := by
  apply Module.ext'
  intro r x
  change dR.smul r (dS.smul (1 : Sᵐᵒᵖ) x) = dR.smul r x
  exact congrArg (dR.smul r) (dS.one_smul x)

/-- For the enveloping module built from specified commuting
actions on M, restricting to Sᵒᵖ recovers the given
right S-module structure on M. -/
theorem ofActions_rightModule : rightModule R S (ofActions R S M) = dS := by
  apply Module.ext'
  intro t x
  change dR.smul (1 : R) (dS.smul t x) = dS.smul t x
  exact dR.one_smul (dS.smul t x)

/-- For the enveloping module formed from specified endpoint
actions on M, integer scalar restriction recovers the
given ℤ-module structure. -/
theorem ofActions_groundModule : groundModule R S (ofActions R S M) = dM := by
  apply Module.ext'
  intro c x
  change (moduleOfActions R S M).smul (algebraMap ℤ (R ⊗[ℤ] Sᵐᵒᵖ) c) x =
    dM.smul c x
  rw [Algebra.TensorProduct.algebraMap_apply]
  change dR.smul (algebraMap ℤ R c) (dS.smul (1 : Sᵐᵒᵖ) x) = dM.smul c x
  have hOne : dS.smul (1 : Sᵐᵒᵖ) x = x := dS.one_smul x
  have hCast : dR.smul (algebraMap ℤ R c) x = dM.smul c x :=
    (Int.cast_smul_eq_zsmul R c (show M from x)).trans
      (int_smul_eq_zsmul dM c (show M from x)).symm
  exact (congrArg (dR.smul (algebraMap ℤ R c)) hOne).trans hCast

end GivenActions

section SemilinearMaps

variable (φ : R →+* R') (ψ : S →+* S')
  (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ))
  (B' : ModuleCat.{b'} (R' ⊗[ℤ] S'ᵐᵒᵖ))

/-- For φ:R→R′ and ψ:S→S′, a map B→B′ semilinear along
φ⊗ψᵒᵖ gives a φ-semilinear map between the restricted
left endpoint modules. Its underlying additive function is unchanged. -/
def toLeftSemilinearMap (f : B →ₛₗ[envelopingRingHom φ ψ] B') :
    letI := leftModule R S B
    letI := leftModule R' S' B'
    B →ₛₗ[φ] B' := by
  letI := leftModule R S B
  letI := leftModule R' S' B'
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro r x
  change f (B.isModule.smul (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) x) =
    B'.isModule.smul (φ r ⊗ₜ[ℤ] (1 : S'ᵐᵒᵖ)) (f x)
  have h := f.map_smul' (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) x
  rw [envelopingRingHom_tmul, map_one] at h
  exact h

/-- For φ:R→R′ and ψ:S→S′, a map B→B′ semilinear along
the enveloping map gives a ψᵒᵖ-semilinear map between
the right endpoint modules on the same carriers. -/
def toRightSemilinearMap (f : B →ₛₗ[envelopingRingHom φ ψ] B') :
    letI := rightModule R S B
    letI := rightModule R' S' B'
    B →ₛₗ[ψ.op] B' := by
  letI := rightModule R S B
  letI := rightModule R' S' B'
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro t x
  change f (B.isModule.smul ((1 : R) ⊗ₜ[ℤ] t) x) =
    B'.isModule.smul ((1 : R') ⊗ₜ[ℤ] ψ.op t) (f x)
  have h := f.map_smul' ((1 : R) ⊗ₜ[ℤ] t) x
  rw [envelopingRingHom_tmul, map_one] at h
  exact h

/-- For an enveloping-semilinear map f:B→B′ along
φ⊗ψᵒᵖ, the left actions satisfy
f(r•x)=φ(r)•f(x) for every r∈R and x∈B. -/
theorem map_left_smul (f : B →ₛₗ[envelopingRingHom φ ψ] B') (r : R) (x : B) :
    f ((leftModule R S B).smul r x) =
      (leftModule R' S' B').smul (φ r) (f x) := by
  let := leftModule R S B
  let := leftModule R' S' B'
  change f (B.isModule.smul (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) x) =
    B'.isModule.smul (φ r ⊗ₜ[ℤ] (1 : S'ᵐᵒᵖ)) (f x)
  have h := f.map_smul' (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) x
  rw [envelopingRingHom_tmul, map_one] at h
  exact h

/-- For an enveloping-semilinear map f:B→B′ along
φ⊗ψᵒᵖ, the right actions satisfy
f(t•x)=ψᵒᵖ(t)•f(x) for every t∈Sᵒᵖ and x∈B. -/
theorem map_right_smul (f : B →ₛₗ[envelopingRingHom φ ψ] B')
    (t : Sᵐᵒᵖ) (x : B) :
    f ((rightModule R S B).smul t x) =
      (rightModule R' S' B').smul (ψ.op t) (f x) := by
  let := rightModule R S B
  let := rightModule R' S' B'
  change f (B.isModule.smul ((1 : R) ⊗ₜ[ℤ] t) x) =
    B'.isModule.smul ((1 : R') ⊗ₜ[ℤ] ψ.op t) (f x)
  have h := f.map_smul' ((1 : R) ⊗ₜ[ℤ] t) x
  rw [envelopingRingHom_tmul, map_one] at h
  exact h

/-- For an additive map f:B→B′, assume
f(r•x)=φ(r)•f(x) and f(t•x)=ψᵒᵖ(t)•f(x)
for all endpoint scalars. Then f is semilinear over
E_(R,S)→E_(R′,S′), without a separate enveloping-linearity premise. -/
def ofSemilinearMap (f : B →+ B')
    (hL : ∀ (r : R) (x : B), f ((leftModule R S B).smul r x) =
      (leftModule R' S' B').smul (φ r) (f x))
    (hR : ∀ (t : Sᵐᵒᵖ) (x : B), f ((rightModule R S B).smul t x) =
      (rightModule R' S' B').smul (ψ.op t) (f x)) :
    B →ₛₗ[envelopingRingHom φ ψ] B' := by
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro z x
  change f (B.isModule.smul z x) = B'.isModule.smul (envelopingRingHom φ ψ z) (f x)
  induction z using TensorProduct.inductionOn with
  | tmul r t =>
    rw [smul_tmul, envelopingRingHom_tmul, smul_tmul, hL, hR]
  | add z w hz hw =>
    have hSource : B.isModule.smul (z + w) x =
        B.isModule.smul z x + B.isModule.smul w x := B.isModule.add_smul z w x
    have hTarget : B'.isModule.smul (envelopingRingHom φ ψ (z + w)) (f x) =
        B'.isModule.smul (envelopingRingHom φ ψ z) (f x) +
          B'.isModule.smul (envelopingRingHom φ ψ w) (f x) := by
      rw [(envelopingRingHom φ ψ).map_add]
      exact B'.isModule.add_smul _ _ _
    exact (congrArg f hSource).trans
      ((f.map_add _ _).trans ((congrArg₂ (fun a b : B' => a + b) hz hw).trans hTarget.symm))

/-- For an additive map f satisfying the left and right
endpoint semilinearity equations, the resulting
enveloping-semilinear map sends x to f(x). -/
theorem ofSemilinearMap_apply (f : B →+ B') (hL hR) (x : B) :
    ofSemilinearMap φ ψ B B' f hL hR x = f x := rfl

/-- For ring maps φ:R→R′ and ψ:S→S′, enveloping-semilinear
maps B→B′ are in bijection with additive maps satisfying
the φ-left and ψᵒᵖ-right scalar equations.
The coefficient carrier worlds b,b′ are independent,
and the correspondence is a plain equivalence of sets. -/
def semilinearEquiv :
    (B →ₛₗ[envelopingRingHom φ ψ] B') ≃
      {f : B →+ B' //
        (∀ (r : R) (x : B), f ((leftModule R S B).smul r x) =
          (leftModule R' S' B').smul (φ r) (f x)) ∧
        (∀ (t : Sᵐᵒᵖ) (x : B), f ((rightModule R S B).smul t x) =
          (rightModule R' S' B').smul (ψ.op t) (f x))} where
  toFun f := ⟨f.toAddMonoidHom, map_left_smul φ ψ B B' f,
    map_right_smul φ ψ B B' f⟩
  invFun f := ofSemilinearMap φ ψ B B' f.1 f.2.1 f.2.2
  left_inv f := by
    apply LinearMap.ext
    intro x
    rfl
  right_inv f := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    rfl

end SemilinearMaps

/-- For φ:R→R′ and ψ:S→S′, restriction along
φ⊗ψᵒᵖ gives ModuleCat^b(E_(R′,S′))→ModuleCat^b(E_(R,S)).
It retains the coefficient carrier and restricts both endpoint actions. -/
abbrev restrictFunctor (φ : R →+* R') (ψ : S →+* S') :
    ModuleCat.{b} (R' ⊗[ℤ] S'ᵐᵒᵖ) ⥤ ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ) :=
  ModuleCat.restrictScalars (envelopingRingHom φ ψ)

/-- For an E_(R′,S′)-module B′, its left R-action after
enveloping restriction is r•x=φ(r)•x.
This is the left endpoint module restricted along φ. -/
theorem restrict_leftModule (φ : R →+* R') (ψ : S →+* S')
    (B' : ModuleCat.{b} (R' ⊗[ℤ] S'ᵐᵒᵖ)) :
    letI := leftModule R' S' B'
    leftModule R S ((restrictFunctor φ ψ).obj B') = Module.compHom B' φ := by
  let := leftModule R' S' B'
  apply Module.ext'
  intro r x
  change B'.isModule.smul (envelopingRingHom φ ψ (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ))) x =
    B'.isModule.smul (φ r ⊗ₜ[ℤ] (1 : S'ᵐᵒᵖ)) x
  rw [envelopingRingHom_tmul, map_one]

/-- For an E_(R′,S′)-module B′, its right S-action after
enveloping restriction is t•x=ψᵒᵖ(t)•x.
This is its right endpoint module restricted along ψᵒᵖ. -/
theorem restrict_rightModule (φ : R →+* R') (ψ : S →+* S')
    (B' : ModuleCat.{b} (R' ⊗[ℤ] S'ᵐᵒᵖ)) :
    letI := rightModule R' S' B'
    rightModule R S ((restrictFunctor φ ψ).obj B') = Module.compHom B' ψ.op := by
  let := rightModule R' S' B'
  apply Module.ext'
  intro t x
  change B'.isModule.smul (envelopingRingHom φ ψ ((1 : R) ⊗ₜ[ℤ] t)) x =
    B'.isModule.smul ((1 : R') ⊗ₜ[ℤ] ψ.op t) x
  rw [envelopingRingHom_tmul, map_one]

/-- For rings R,S, the enveloping map induced by id_R
and id_S is id on R⊗[ℤ]Sᵒᵖ. -/
theorem envelopingRingHom_id :
    envelopingRingHom (RingHom.id R) (RingHom.id S) = RingHom.id (R ⊗[ℤ] Sᵐᵒᵖ) := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r t => rw [envelopingRingHom_tmul]; rfl
  | add z w hz hw =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hw

variable {R'' : Type r''} {S'' : Type s''} [Ring R''] [Ring S'']

/-- For composable endpoint maps φ,φ′ and ψ,ψ′,
(φ′⊗ψ′ᵒᵖ)∘(φ⊗ψᵒᵖ) is the enveloping map of
φ′∘φ and ψ′∘ψ. All ring worlds are independent. -/
theorem envelopingRingHom_comp (φ : R →+* R') (ψ : S →+* S')
    (φ' : R' →+* R'') (ψ' : S' →+* S'') :
    (envelopingRingHom φ' ψ').comp (envelopingRingHom φ ψ) =
      envelopingRingHom (φ'.comp φ) (ψ'.comp ψ) := by
  apply RingHom.ext
  intro z
  change envelopingRingHom φ' ψ' (envelopingRingHom φ ψ z) =
    envelopingRingHom (φ'.comp φ) (ψ'.comp ψ) z
  induction z using TensorProduct.inductionOn with
  | tmul r t =>
    rw [envelopingRingHom_tmul, envelopingRingHom_tmul, envelopingRingHom_tmul]
    rfl
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]

/-- Restriction along id_R and id_S is naturally
isomorphic to the identity functor on E_(R,S)-modules.
The component maps retain the underlying coefficient values. -/
def restrictId :
    restrictFunctor (RingHom.id R) (RingHom.id S) ≅
      𝟭 (ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) :=
  ModuleCat.restrictScalarsId' (envelopingRingHom (RingHom.id R) (RingHom.id S))
    envelopingRingHom_id

/-- For R→R′→R″ and S→S′→S″, restriction along the
composite endpoint maps is naturally isomorphic to first
restricting from R″,S″ to R′,S′ and then to R,S.
The coefficient carrier is unchanged. -/
def restrictComp (φ : R →+* R') (ψ : S →+* S')
    (φ' : R' →+* R'') (ψ' : S' →+* S'') :
    restrictFunctor (φ'.comp φ) (ψ'.comp ψ) ≅
      restrictFunctor φ' ψ' ⋙ restrictFunctor φ ψ :=
  ModuleCat.restrictScalarsComp' (envelopingRingHom φ ψ) (envelopingRingHom φ' ψ')
    (envelopingRingHom (φ'.comp φ) (ψ'.comp ψ))
    (envelopingRingHom_comp φ ψ φ' ψ').symm

/-- For an E_(R″,S″)-module B″, the forward component
identifying composite endpoint restriction with two successive
restrictions sends every x∈B″ to itself. -/
theorem restrictComp_hom_apply (φ : R →+* R') (ψ : S →+* S')
    (φ' : R' →+* R'') (ψ' : S' →+* S'')
    (B'' : ModuleCat.{b} (R'' ⊗[ℤ] S''ᵐᵒᵖ)) (x : B'') :
    ((restrictComp φ ψ φ' ψ').hom.app B'').hom x = x := rfl

/-- For an E_(R″,S″)-module B″, the inverse component
of the endpoint restriction-composition isomorphism sends
every underlying value x to itself. -/
theorem restrictComp_inv_apply (φ : R →+* R') (ψ : S →+* S')
    (φ' : R' →+* R'') (ψ' : S' →+* S'')
    (B'' : ModuleCat.{b} (R'' ⊗[ℤ] S''ᵐᵒᵖ)) (x : B'') :
    ((restrictComp φ ψ φ' ψ').inv.app B'').hom x = x := rfl

end ModuleCat.Bimodule.RingChange
