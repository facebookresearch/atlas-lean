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
# Native bimodule restriction with independent endpoint rings

An R–S bimodule is the existing native category object over
`R ⊗[ℤ] Sᵐᵒᵖ`. Its endpoint restrictions commute by multiplication of the
two tensor inclusions. Changing R and S uses the native tensor algebra map
and `ModuleCat.restrictScalars`. Semilinear maps are characterized by the
two original endpoint equations, with independent carrier universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe r r' r'' s s' s'' b b'

namespace ModuleCat.Bimodule.RingChange

variable {R : Type r} {S : Type s} [Ring R] [Ring S]
  {R' : Type r'} {S' : Type s'} [Ring R'] [Ring S']

/-- The actual map of the two native enveloping rings, without commutative endpoints. -/
def envelopingRingHom (φ : R →+* R') (ψ : S →+* S') :
    R ⊗[ℤ] Sᵐᵒᵖ →+* R' ⊗[ℤ] S'ᵐᵒᵖ :=
  (Algebra.TensorProduct.map φ.toIntAlgHom ψ.op.toIntAlgHom).toRingHom

/-- Pure enveloping scalars retain their two separately mapped endpoints. -/
theorem envelopingRingHom_tmul (φ : R →+* R') (ψ : S →+* S')
    (r : R) (t : Sᵐᵒᵖ) :
    envelopingRingHom φ ψ (r ⊗ₜ[ℤ] t) = φ r ⊗ₜ[ℤ] ψ.op t :=
  Algebra.TensorProduct.map_tmul φ.toIntAlgHom ψ.op.toIntAlgHom r t

/-- The native endpoint restriction along the first tensor inclusion. -/
def leftModule (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) : Module R B :=
  Module.compHom B
    (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℤ] Sᵐᵒᵖ)

/-- The native endpoint restriction along the second tensor inclusion. -/
def rightModule (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) : Module Sᵐᵒᵖ B :=
  Module.compHom B
    (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[ℤ] R ⊗[ℤ] Sᵐᵒᵖ).toRingHom

/-- The original integer action is native restriction of the stored enveloping action. -/
def groundModule (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) : Module ℤ B :=
  Module.compHom B (Int.castRingHom (R ⊗[ℤ] Sᵐᵒᵖ))

/-- The actual two endpoint actions commute; no commuting-action conclusion is an input. -/
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

/-- The original pure enveloping scalar is the ordered pair of endpoint actions. -/
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

/-- Combine the given original actions with the native module constructor.
The supplied integer dictionary is passed explicitly and its towers are earned. -/
def moduleOfActions : Module (R ⊗[ℤ] Sᵐᵒᵖ) M :=
  @TensorProduct.Algebra.module ℤ R Sᵐᵒᵖ M
    inferInstance (inferInstance : AddCommMonoid M) dM
    inferInstance inferInstance dR dS inferInstance inferInstance
    (Module.intModule_isScalarTower (Algebra.toModule : Module ℤ R) dM)
    (Module.intModule_isScalarTower (Algebra.toModule : Module ℤ Sᵐᵒᵖ) dM)
    inferInstance

/-- Bundle the given carrier and the earned native enveloping module. -/
def ofActions : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ) :=
  letI := moduleOfActions R S M
  ModuleCat.of (R ⊗[ℤ] Sᵐᵒᵖ) M

/-- The first native restriction recovers the actual given left module dictionary. -/
theorem ofActions_leftModule : leftModule R S (ofActions R S M) = dR := by
  apply Module.ext'
  intro r x
  change dR.smul r (dS.smul (1 : Sᵐᵒᵖ) x) = dR.smul r x
  exact congrArg (dR.smul r) (dS.one_smul x)

/-- The second native restriction recovers the actual given right module dictionary. -/
theorem ofActions_rightModule : rightModule R S (ofActions R S M) = dS := by
  apply Module.ext'
  intro t x
  change dR.smul (1 : R) (dS.smul t x) = dS.smul t x
  exact dR.one_smul (dS.smul t x)

/-- Native integer restriction also recovers the supplied original integer dictionary. -/
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

/-- A native semilinear enveloping map restricts to the original left actions. -/
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

/-- The second endpoint restriction is semilinear for the actual opposite ring map. -/
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

/-- Its left scalar equation refers to the original endpoint module data. -/
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

/-- Its right scalar equation likewise uses the original opposite endpoint. -/
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

/-- The two original equivariance equations earn native enveloping semilinearity. -/
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

/-- The map constructed from the original endpoint equations keeps the original function. -/
theorem ofSemilinearMap_apply (f : B →+ B') (hL hR) (x : B) :
    ofSemilinearMap φ ψ B B' f hL hR x = f x := rfl

/-- Complete characterization of the native semilinear bimodule maps. -/
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

/-- Restriction is the native module category functor along the earned tensor ring map. -/
abbrev restrictFunctor (φ : R →+* R') (ψ : S →+* S') :
    ModuleCat.{b} (R' ⊗[ℤ] S'ᵐᵒᵖ) ⥤ ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ) :=
  ModuleCat.restrictScalars (envelopingRingHom φ ψ)

/-- Simultaneous enveloping restriction has the genuine original left ring restriction. -/
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

/-- The actual right endpoint restriction is independently along `ψ.op`. -/
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

/-- Identity endpoint maps recover the native enveloping identity ring map. -/
theorem envelopingRingHom_id :
    envelopingRingHom (RingHom.id R) (RingHom.id S) = RingHom.id (R ⊗[ℤ] Sᵐᵒᵖ) := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r t => rw [envelopingRingHom_tmul]; rfl
  | add z w hz hw =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hw

variable {R'' : Type r''} {S'' : Type s''} [Ring R''] [Ring S'']

/-- The composite tensor ring map changes each noncommutative endpoint in its own order. -/
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

/-- The identity coherence is the native carrier-preserving restriction isomorphism. -/
def restrictId :
    restrictFunctor (RingHom.id R) (RingHom.id S) ≅
      𝟭 (ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) :=
  ModuleCat.restrictScalarsId' (envelopingRingHom (RingHom.id R) (RingHom.id S))
    envelopingRingHom_id

/-- Composition coherence is native scalar restriction along the proved composite map. -/
def restrictComp (φ : R →+* R') (ψ : S →+* S')
    (φ' : R' →+* R'') (ψ' : S' →+* S'') :
    restrictFunctor (φ'.comp φ) (ψ'.comp ψ) ≅
      restrictFunctor φ' ψ' ⋙ restrictFunctor φ ψ :=
  ModuleCat.restrictScalarsComp' (envelopingRingHom φ ψ) (envelopingRingHom φ' ψ')
    (envelopingRingHom (φ'.comp φ) (ψ'.comp ψ))
    (envelopingRingHom_comp φ ψ φ' ψ').symm

/-- The restriction composition comparison is the actual identity on each coefficient. -/
theorem restrictComp_hom_apply (φ : R →+* R') (ψ : S →+* S')
    (φ' : R' →+* R'') (ψ' : S' →+* S'')
    (B'' : ModuleCat.{b} (R'' ⊗[ℤ] S''ᵐᵒᵖ)) (x : B'') :
    ((restrictComp φ ψ φ' ψ').hom.app B'').hom x = x := rfl

/-- Its inverse has the same carrier identity. -/
theorem restrictComp_inv_apply (φ : R →+* R') (ψ : S →+* S')
    (φ' : R' →+* R'') (ψ' : S' →+* S'')
    (B'' : ModuleCat.{b} (R'' ⊗[ℤ] S''ᵐᵒᵖ)) (x : B'') :
    ((restrictComp φ ψ φ' ψ').inv.app B'').hom x = x := rfl

end ModuleCat.Bimodule.RingChange
