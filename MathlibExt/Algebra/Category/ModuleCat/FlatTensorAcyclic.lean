/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.ProjectiveFlatTargetTensor
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Logic.Small.Defs

/-!
# Tensor acyclicity of a flat resolved module

For a commutative ring `R` in universe `u`, coefficient module `M`
in universe `v`, and flat module `X` in universe `max(u,w)`,
tensoring a projective resolution of `X` with `M` has zero positive
homology. Hence `X` has zero positive left-derived values for
`M ⊗[R] -`. Modules with independent original carriers are treated
by lifting the target to the source world containing the ring.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat.FlatTensorAcyclic

variable (R : Type u) [CommRing R]
  (M : ModuleCat.{v} R)

/-- For a ring carrier `R` in universe `u`, it has a small
presentation in the common source universe `max(u,w)`. -/
local instance ringSmall : Small.{max u w} R := small_max R
/-- For a commutative ring `R` in universe `u`, the category
`ModuleCat_max(u,w)(R)` has enough projectives, using free-module
presentations within the world containing the ring. -/
local instance enoughProjectives : EnoughProjectives (ModuleCat.{max u w} R) :=
  ModuleCat.enoughProjectives
/-- For a commutative ring `R` in universe `u`, enough projectives
in `ModuleCat_max(u,w)(R)` give projective resolutions of its objects. -/
local instance hasProjectiveResolutions : HasProjectiveResolutions (ModuleCat.{max u w} R) :=
  inferInstance

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. If `X` is flat, any projective resolution `P` of `X` computes
zero values `L_(n+1)(M ⊗[R] -)(X)` in every positive degree. -/
theorem isZero_leftDerived_obj_of_projectiveResolution
    (X : ModuleCat.{max u w} R) [Module.Flat R X]
    (P : ProjectiveResolution X) (n : ℕ) :
    IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj M).leftDerived (n + 1)).obj X) := by
  have h : IsZero ((ModuleCat.projectiveCoefficientComplex R M P).homology (n + 1)) :=
    ModuleCat.projectiveCoefficientHomology_isZero_succ R M P n
  exact IsZero.of_iso h
    (P.isoLeftDerivedObj ((tensorBifunctorAt.{u, v, max u w} R).obj M) (n + 1))

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. If `X` is flat, its left-derived tensor values
`L_(n+1)(M ⊗[R] -)(X)` are zero for every `n ∈ ℕ`. -/
theorem isZero_leftDerived_obj (X : ModuleCat.{max u w} R) [Module.Flat R X] (n : ℕ) :
    IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj M).leftDerived (n + 1)).obj X) :=
  isZero_leftDerived_obj_of_projectiveResolution R M X (projectiveResolution X) n

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. For flat `X`, the entire family of positive left-derived
values of the fixed-coefficient tensor functor is zero. -/
theorem all_positive_isZero (X : ModuleCat.{max u w} R) [Module.Flat R X] :
    ∀ n : ℕ,
      IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj M).leftDerived (n + 1)).obj X) :=
  fun n => isZero_leftDerived_obj R M X n

/-- Let `R` be commutative in universe `u`, `M` an `R`-module in
universe `v`, and `Q` a chain complex in `ModuleCat_max(u,w)(R)`.
If every term `Q_q` is flat, then
`L_(n+1)(M ⊗[R] -)(Q_q)=0` for every `q,n`. -/
theorem termwise_all_positive_isZero (Q : ChainComplex (ModuleCat.{max u w} R) ℕ)
    [∀ q, Module.Flat R (Q.X q)] :
    ∀ q n : ℕ,
      IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj M).leftDerived (n + 1)).obj (Q.X q)) :=
  fun q n => isZero_leftDerived_obj R M (Q.X q) n

section OriginalCarriers

variable (M₀ : Type v) (X₀ : Type w)
  [AddCommGroup M₀] [AddCommGroup X₀] [Module R M₀] [Module R X₀]

/-- Let `R` be commutative in universe `u`, `M₀` an `R`-module
with carrier in `v`, and `X₀` a flat `R`-module with carrier in `w`.
After lifting `X₀` to `max(u,w)`, all positive left-derived values
of `M₀ ⊗[R] -` on that target vanish. -/
theorem originalCarrier_all_positive_isZero [Module.Flat R X₀] :
    ∀ n : ℕ,
      IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj (ModuleCat.of R M₀)).leftDerived
        (n + 1)).obj (ModuleCat.of R (ULift.{u} X₀))) := by
  let : Module.Flat R (ModuleCat.of R (ULift.{u} X₀)) :=
    Module.Flat.of_linearEquiv (ULift.moduleEquiv : ULift.{u} X₀ ≃ₗ[R] X₀)
  exact all_positive_isZero R (ModuleCat.of R M₀) (ModuleCat.of R (ULift.{u} X₀))

end OriginalCarriers

end ModuleCat.FlatTensorAcyclic
