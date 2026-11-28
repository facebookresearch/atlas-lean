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
# Associated graded module pieces and first-order maps

Let `R` be a commutative ring, `I` an ideal, and `M` an `R`-module. The degree-`n` piece is
`I^n M/I^(n+1) M`, represented by quotienting `I^n M` by its submodule `I(I^n M)`. The
initial-form map sends a representative to its class.

An `R`-linear map `f : M → N` induces an `R/I`-linear map on each degree, with `[x]_n ↦ [f
x]_n`. In degree one the layer is `IM/I(IM) = IM/I²M`.

If the range of `f : M → N` lies in `IN`, its first-order linearization is the `R/I`-linear
map `M/IM → IN/I²N` sending `[m]` to `[f m]`.

References: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapters 2 and 10.
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

/-- Let `R` be a commutative ring, `I : Ideal R`, `M` an `R`-module, and `n : ℕ`. The degree-`n`
associated graded module piece is `I^n M/I^(n+1) M`. Its quotient presentation is `I^n M ⧸
I(I^n M)`, where `I^n M = I^n • (⊤ : Submodule R M)` and the denominator is taken inside that
submodule. -/
abbrev AssociatedGradedModulePiece
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type v :=
  ↥(I ^ n • (⊤ : Submodule R M)) ⧸
    (I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))))

/-- For a commutative ring `R`, an ideal `I`, an `R`-module `M`, and `n : ℕ`, this is the
`R`-linear quotient map `I^n M → I^n M/I^(n+1) M`. It sends a representative `x : I^n M` to
`Submodule.Quotient.mk x`. -/
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

/-- For a commutative ring `R`, an ideal `I`, an `R`-module `M`, and every `n : ℕ`,
`initialFormModule I M n : I^n M → I.AssociatedGradedModulePiece M n` is surjective. Every
degree-`n` class is represented by an element of `I^n M`. -/
theorem initialFormModule_surjective (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Surjective (initialFormModule I M n) :=
  Submodule.mkQ_surjective _

/-- Let `R` be a commutative ring, `I` an ideal, `M` an `R`-module, `n : ℕ`, and `x : I^n M`. Then
`initialFormModule I M n x = 0` if and only if the underlying element `(x : M)` lies in
`I^(n+1) M`. -/
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

/-- Let `R` be a commutative ring, `I : Ideal R`, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. For
`n : ℕ`, this is the induced `R/I`-linear map `I^n M/I^(n+1) M → I^n N/I^(n+1) N`, sending
`[x]_n` to `[f x]_n`. -/
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

/-- Let `R` be a commutative ring, `I` an ideal, `M,N` be `R`-modules, and `f : M →ₗ[R] N` a
surjective map. For every `n : ℕ`, the induced map `associatedGradedModuleMap I f n : I^n
M/I^(n+1) M → I^n N/I^(n+1) N` is surjective. -/
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

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, the first-order layer is
`IM/I(IM)`, represented as `↥(I • ⊤) ⧸ (I • ⊤)` with the denominator inside `IM`. Under the
inclusion `IM ⊆ M`, this denominator is `I²M`, so the layer is `IM/I²M`. -/
abbrev FirstOrderModuleLayer
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Type v :=
  ↥(I • (⊤ : Submodule R M)) ⧸
    (I • (⊤ : Submodule R ↥(I • (⊤ : Submodule R M))))

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, this is the `R/I`-linear
equivalence `I.FirstOrderModuleLayer M ≃ₗ[R/I] I.AssociatedGradedModulePiece M 1`. Both sides
are `IM/I²M`, and the equivalence preserves each representative in `IM`. -/
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

/-- Let `R` be a commutative ring, `I` an ideal, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. The
induced `R/I`-linear map `IM/I²M → IN/I²N` sends a class represented by `x ∈ IM` to the class
represented by `f x ∈ IN`. -/
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

/-- Let `R` be a commutative ring, `I : Ideal R`, and `M,N` be `R`-modules. If `f : M →ₗ[R] N`
satisfies `LinearMap.range f ≤ IN`, then its layer-valued linearization is an `R/I`-linear map
`M/IM → IN/I²N`. It sends the quotient class of `m : M` to the first-order class of `f m`. -/
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
