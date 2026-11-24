/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Associated-graded pieces of modules

For an ideal `I` and an `R`-module `M`, this file defines the degree-`n`
piece `I ^ n M / I ^ (n + 1) M`, its initial-form map, and functoriality in
`M`. It also exposes the first-order layer `IM / I(IM)` and the raw
linearization of a map whose range lies in `IN`.

No total graded-module structure, Rees module, flatness theorem, or
first-order tensor comparison is introduced here.

## Main declarations

* `Ideal.AssociatedGradedModulePiece`
* `Ideal.initialFormModule`
* `Ideal.associatedGradedModuleMap`
* `Ideal.FirstOrderModuleLayer`
* `Ideal.firstOrderLayerMap`
* `LinearMap.linearizedLayer`
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open scoped Pointwise

universe u v w

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The degree-`n` associated-graded piece `I ^ n M / I ^ (n + 1) M` of an
`R`-module, presented as the quotient of `I ^ n M` by `I` times that
submodule. -/
abbrev AssociatedGradedModulePiece
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type v :=
  ↥(I ^ n • (⊤ : Submodule R M)) ⧸
    (I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))))

/-- The class of an element of `I ^ n M` in the degree-`n`
associated-graded module piece. -/
def initialFormModule (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    ↥(I ^ n • (⊤ : Submodule R M)) →ₗ[R]
      I.AssociatedGradedModulePiece M n :=
  Submodule.mkQ _

@[simp]
theorem initialFormModule_apply (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ)
    (x : ↥(I ^ n • (⊤ : Submodule R M))) :
    initialFormModule I M n x = Submodule.Quotient.mk x :=
  rfl

/-- Every associated-graded module class has a representative in
`I ^ n M`. -/
theorem initialFormModule_surjective (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Surjective (initialFormModule I M n) :=
  Submodule.mkQ_surjective _

/-- An initial form vanishes exactly when its representative belongs to the
next ideal-power multiple. -/
theorem initialFormModule_eq_zero_iff (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ)
    (x : ↥(I ^ n • (⊤ : Submodule R M))) :
    initialFormModule I M n x = 0 ↔
      (x : M) ∈ I ^ (n + 1) • (⊤ : Submodule R M) := by
  rw [initialFormModule_apply, Submodule.Quotient.mk_eq_zero]
  rw [Submodule.mem_smul_top_iff, pow_succ', ← Submodule.mul_smul]

private def associatedGradedModuleMapRestricted
    (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    ↥(I ^ n • (⊤ : Submodule R M)) →ₗ[R]
      ↥(I ^ n • (⊤ : Submodule R N)) :=
  (f.domRestrict (I ^ n • (⊤ : Submodule R M))).codRestrict
    (I ^ n • (⊤ : Submodule R N)) fun x ↦
      (Submodule.smul_top_le_comap_smul_top (I ^ n) f) x.2

/-- A linear map induces a map on every associated-graded module piece. -/
def associatedGradedModuleMap (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.AssociatedGradedModulePiece M n →ₗ[R ⧸ I]
      I.AssociatedGradedModulePiece N n :=
  (associatedGradedModuleMapRestricted I f n).reduceModIdeal I

@[simp]
theorem associatedGradedModuleMap_initialFormModule
    (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ)
    (x : ↥(I ^ n • (⊤ : Submodule R M))) :
    associatedGradedModuleMap I f n (Submodule.Quotient.mk x) =
      initialFormModule I N n
        ⟨f x, (Submodule.smul_top_le_comap_smul_top (I ^ n) f) x.2⟩ :=
  LinearMap.reduceModIdeal_apply I _ x

@[simp]
theorem associatedGradedModuleMap_id (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    associatedGradedModuleMap I (LinearMap.id : M →ₗ[R] M) n =
      LinearMap.id := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := initialFormModule_surjective I M n y
  change associatedGradedModuleMap I (LinearMap.id : M →ₗ[R] M) n
      (initialFormModule I M n x) = initialFormModule I M n x
  calc
    _ = initialFormModule I M n
        ⟨(LinearMap.id : M →ₗ[R] M) x,
          (Submodule.smul_top_le_comap_smul_top (I ^ n)
            (LinearMap.id : M →ₗ[R] M)) x.2⟩ :=
      associatedGradedModuleMap_initialFormModule I _ n x
    _ = initialFormModule I M n x := by
      congr 1

theorem associatedGradedModuleMap_comp (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    associatedGradedModuleMap I (g.comp f) n =
      (associatedGradedModuleMap I g n).comp
        (associatedGradedModuleMap I f n) := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := initialFormModule_surjective I M n q
  let y : ↥(I ^ n • (⊤ : Submodule R N)) :=
    ⟨f x, (Submodule.smul_top_le_comap_smul_top (I ^ n) f) x.2⟩
  let z₁ : ↥(I ^ n • (⊤ : Submodule R P)) :=
    ⟨(g.comp f) x,
      (Submodule.smul_top_le_comap_smul_top (I ^ n) (g.comp f)) x.2⟩
  let z₂ : ↥(I ^ n • (⊤ : Submodule R P)) :=
    ⟨g y, (Submodule.smul_top_le_comap_smul_top (I ^ n) g) y.2⟩
  change associatedGradedModuleMap I (g.comp f) n
      (initialFormModule I M n x) =
    associatedGradedModuleMap I g n
      (associatedGradedModuleMap I f n (initialFormModule I M n x))
  calc
    _ = initialFormModule I P n z₁ :=
      associatedGradedModuleMap_initialFormModule I _ n x
    _ = initialFormModule I P n z₂ := by
      congr 1
    _ = associatedGradedModuleMap I g n (initialFormModule I N n y) :=
      (associatedGradedModuleMap_initialFormModule I g n y).symm
    _ = associatedGradedModuleMap I g n
        (associatedGradedModuleMap I f n (initialFormModule I M n x)) := by
      exact congrArg (associatedGradedModuleMap I g n)
        (associatedGradedModuleMap_initialFormModule I f n x).symm

/-- A surjective linear map induces a surjective map on every
associated-graded module piece. -/
theorem associatedGradedModuleMap_surjective (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (associatedGradedModuleMap I f n) := by
  intro q
  obtain ⟨y, rfl⟩ := initialFormModule_surjective I N n q
  have hmap : Submodule.map f (I ^ n • (⊤ : Submodule R M)) =
      I ^ n • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr hf]
  have hy : (y : N) ∈ Submodule.map f
      (I ^ n • (⊤ : Submodule R M)) := by
    rw [hmap]
    exact y.2
  rw [Submodule.mem_map] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  let x' : ↥(I ^ n • (⊤ : Submodule R M)) := ⟨x, hx⟩
  refine ⟨initialFormModule I M n x', ?_⟩
  rw [initialFormModule_apply, associatedGradedModuleMap_initialFormModule]
  apply congrArg (initialFormModule I N n)
  exact Subtype.ext hxy

/-- The first-order ideal-adic layer `IM / I(IM)`. -/
abbrev FirstOrderModuleLayer
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Type v :=
  ↥(I • (⊤ : Submodule R M)) ⧸
    (I • (⊤ : Submodule R ↥(I • (⊤ : Submodule R M))))

/-- The direct first-order carrier agrees with the degree-one
associated-graded module piece. -/
@[no_expose]
def firstOrderModuleLayerEquivGradedPiece (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    I.FirstOrderModuleLayer M ≃ₗ[R ⧸ I]
      I.AssociatedGradedModulePiece M 1 := by
  let A : Submodule R M := I • ⊤
  let B : Submodule R M := I ^ 1 • ⊤
  let e : A ≃ₗ[R] B := LinearEquiv.ofEq A B (by simp [A, B])
  let eQ : (A ⧸ (I • ⊤ : Submodule R A)) ≃ₗ[R]
      (B ⧸ (I • ⊤ : Submodule R B)) :=
    Submodule.Quotient.equiv _ _ e (by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr e.surjective])
  exact eQ.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

private def firstOrderLayerMapRestricted (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    ↥(I • (⊤ : Submodule R M)) →ₗ[R]
      ↥(I • (⊤ : Submodule R N)) :=
  (f.domRestrict (I • (⊤ : Submodule R M))).codRestrict
    (I • (⊤ : Submodule R N)) fun x ↦
      (Submodule.smul_top_le_comap_smul_top I f) x.2

/-- A linear map induces a map on first-order ideal-adic layers. -/
def firstOrderLayerMap (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    I.FirstOrderModuleLayer M →ₗ[R ⧸ I]
      I.FirstOrderModuleLayer N :=
  (firstOrderLayerMapRestricted I f).reduceModIdeal I

@[simp]
theorem firstOrderLayerMap_mk (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x : ↥(I • (⊤ : Submodule R M))) :
    firstOrderLayerMap I f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨f x, (Submodule.smul_top_le_comap_smul_top I f) x.2⟩ :
          ↥(I • (⊤ : Submodule R N))) :=
  LinearMap.reduceModIdeal_apply I _ x

@[simp]
theorem firstOrderLayerMap_id (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    firstOrderLayerMap I (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  change firstOrderLayerMap I (LinearMap.id : M →ₗ[R] M)
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x
  calc
    _ = Submodule.Quotient.mk
        (⟨(LinearMap.id : M →ₗ[R] M) x,
          (Submodule.smul_top_le_comap_smul_top I
            (LinearMap.id : M →ₗ[R] M)) x.2⟩ :
            ↥(I • (⊤ : Submodule R M))) :=
      firstOrderLayerMap_mk I _ x
    _ = Submodule.Quotient.mk x := by
      congr 1

theorem firstOrderLayerMap_comp (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    firstOrderLayerMap I (g.comp f) =
      (firstOrderLayerMap I g).comp (firstOrderLayerMap I f) := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  let y : ↥(I • (⊤ : Submodule R N)) :=
    ⟨f x, (Submodule.smul_top_le_comap_smul_top I f) x.2⟩
  let z₁ : ↥(I • (⊤ : Submodule R P)) :=
    ⟨(g.comp f) x,
      (Submodule.smul_top_le_comap_smul_top I (g.comp f)) x.2⟩
  let z₂ : ↥(I • (⊤ : Submodule R P)) :=
    ⟨g y, (Submodule.smul_top_le_comap_smul_top I g) y.2⟩
  change firstOrderLayerMap I (g.comp f) (Submodule.Quotient.mk x) =
    firstOrderLayerMap I g
      (firstOrderLayerMap I f (Submodule.Quotient.mk x))
  calc
    _ = Submodule.Quotient.mk z₁ := firstOrderLayerMap_mk I _ x
    _ = Submodule.Quotient.mk z₂ := by
      congr 1
    _ = firstOrderLayerMap I g (Submodule.Quotient.mk y) :=
      (firstOrderLayerMap_mk I g y).symm
    _ = firstOrderLayerMap I g
        (firstOrderLayerMap I f (Submodule.Quotient.mk x)) := by
      exact congrArg (firstOrderLayerMap I g)
        (firstOrderLayerMap_mk I f x).symm

end Ideal

namespace LinearMap

variable {R : Type u} [CommRing R]

/-- The first-order layer-valued linearization of a map whose range lies in
an ideal multiple of the target. -/
def linearizedLayer (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : LinearMap.range f ≤ I • (⊤ : Submodule R N)) :
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I]
      I.FirstOrderModuleLayer N := by
  let IN : Submodule R N := I • ⊤
  let fr : M →ₗ[R] IN :=
    f.codRestrict IN fun x ↦ hf (LinearMap.mem_range_self f x)
  exact fr.reduceModIdeal I

@[simp]
theorem linearizedLayer_mk (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : LinearMap.range f ≤ I • (⊤ : Submodule R N)) (x : M) :
    f.linearizedLayer I hf (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨f x, hf (LinearMap.mem_range_self f x)⟩ :
          ↥(I • (⊤ : Submodule R N))) :=
  LinearMap.reduceModIdeal_apply I _ x

end LinearMap
