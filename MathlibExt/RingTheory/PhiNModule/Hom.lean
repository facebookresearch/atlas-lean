/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.PhiNModule.WeaklyAdmissible

/-!
# The additive structure on morphisms of filtered `(φ, N)`-modules

Let `K₀` be a field with a ring automorphism `σ` (given with its inverse `σ'`), let `p ∈ K₀` and
let `K` be a field extension of `K₀`. The identity map of a `(φ, N)`-module over `K₀` is a
morphism (`PhiNModule.Hom`), and so is the composition of two morphisms; the same holds for
filtered `(φ, N)`-modules over `K` (`FilteredPhiNModule.Hom`). Sums, negatives and differences
of morphisms are morphisms, so the morphisms `M₁ → M₂` form an additive commutative group, and
composition is biadditive.

Morphisms are not stable under multiplication by all scalars of `K₀`: as `φ` is
`σ`-semilinear, `φ (c • η x) = σ c • φ (η x)`, so `c • η` commutes with `φ` only if
`σ c • φ (η x) = c • φ (η x)` for all `x`. For a commutative semiring `R` and an `R`-algebra
structure on `K₀` such that `σ (algebraMap R K₀ r) = algebraMap R K₀ r` for every `r : R`
(assumed as a `Fact`), the morphisms form an `R`-module and composition is `R`-bilinear. In the
setting of Fontaine–Ouyang, `K₀ = W(k)[1/p]`, `σ` is the absolute Frobenius and one can take
`R = ℚ_p`: the filtered `(φ, N)`-modules form an additive `ℚ_p`-linear category (Fontaine,
Exposé III, §4.3.3).

For a stable subspace `D'` of a finite-dimensional filtered `(φ, N)`-module `D`, the inclusion
of `D'` with the induced filtration and the projection onto `D ⧸ D'` with the quotient
filtration are morphisms, and so is the corestriction of a morphism `η` to its image with the
filtration induced from the target.

## Main definitions

* `PhiNModule.Hom.id`, `PhiNModule.Hom.comp`: the identity and the composition of morphisms of
  `(φ, N)`-modules.
* `FilteredPhiNModule.Hom.id`, `FilteredPhiNModule.Hom.comp`: the identity and the composition of
  morphisms of filtered `(φ, N)`-modules.
* The instances `AddCommGroup (M₁.Hom M₂)` and, when `σ` fixes the image of `R` in `K₀`,
  `Module R (M₁.Hom M₂)`, for `PhiNModule.Hom` and for `FilteredPhiNModule.Hom`.
* `FilteredPhiNModule.subtype`, `FilteredPhiNModule.mkQ`: the inclusion of a stable subspace and
  the projection onto the quotient by it.
* `FilteredPhiNModule.Hom.rangeRestrict`: the corestriction of a morphism to its image.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.1 and §8.2.3: Definitions 8.13 (ii) and 8.34 (2).
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.3.3 p. 148.
-/

@[expose] public section

namespace PhiNModule

variable {K₀ : Type*} [Field K₀] {σ σ' : K₀ →+* K₀} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {p : K₀} {D₁ D₂ D₃ D₄ : Type*} [AddCommGroup D₁] [Module K₀ D₁] [AddCommGroup D₂]
  [Module K₀ D₂] [AddCommGroup D₃] [Module K₀ D₃] [AddCommGroup D₄] [Module K₀ D₄]
  {M₁ : PhiNModule σ p D₁} {M₂ : PhiNModule σ p D₂} {M₃ : PhiNModule σ p D₃}
  {M₄ : PhiNModule σ p D₄}

namespace Hom

/-- Two morphisms of `(φ, N)`-modules `M₁ → M₂` with the same underlying `K₀`-linear map are
equal. -/
@[ext]
theorem ext {f g : M₁.Hom M₂} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  congr

/-- A morphism of `(φ, N)`-modules `M₁ → M₂` is determined by its underlying `K₀`-linear map. -/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : M₁.Hom M₂ → D₁ →ₗ[K₀] D₂) := fun _ _ => ext

variable (M₁) in
/-- The identity morphism of a `(φ, N)`-module `M₁`, whose underlying map is the identity. -/
def id : M₁.Hom M₁ where
  toLinearMap := LinearMap.id
  map_φ _ := rfl
  map_N _ := rfl

variable (M₁) in
/-- The `K₀`-linear map underlying the identity morphism of `M₁` is `LinearMap.id`. -/
@[simp]
theorem id_toLinearMap : (id M₁).toLinearMap = LinearMap.id :=
  rfl

/-- The composition `g ∘ f` of morphisms of `(φ, N)`-modules `f : M₁ → M₂` and `g : M₂ → M₃`,
whose underlying map is the composition of the underlying maps. -/
def comp (g : M₂.Hom M₃) (f : M₁.Hom M₂) : M₁.Hom M₃ where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_φ x := by rw [LinearMap.comp_apply, LinearMap.comp_apply, f.map_φ, g.map_φ]
  map_N x := by rw [LinearMap.comp_apply, LinearMap.comp_apply, f.map_N, g.map_N]

/-- The `K₀`-linear map underlying `g.comp f` is `g.toLinearMap ∘ₗ f.toLinearMap`. -/
@[simp]
theorem comp_toLinearMap (g : M₂.Hom M₃) (f : M₁.Hom M₂) :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  rfl

/-- Composing a morphism `f : M₁ → M₂` with the identity of `M₂` gives `f`. -/
@[simp]
theorem id_comp (f : M₁.Hom M₂) : (id M₂).comp f = f :=
  rfl

/-- Composing the identity of `M₁` with a morphism `f : M₁ → M₂` gives `f`. -/
@[simp]
theorem comp_id (f : M₁.Hom M₂) : f.comp (id M₁) = f :=
  rfl

/-- Composition of morphisms of `(φ, N)`-modules is associative. -/
theorem comp_assoc (h : M₃.Hom M₄) (g : M₂.Hom M₃) (f : M₁.Hom M₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/-! ### The additive group of morphisms -/

/-- The zero morphism `M₁ → M₂` of `(φ, N)`-modules, whose underlying map is `0`. -/
instance : Zero (M₁.Hom M₂) :=
  ⟨⟨0, fun _ => by rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero],
    fun _ => by rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]⟩⟩

/-- The sum of two morphisms `M₁ → M₂` of `(φ, N)`-modules, whose underlying map is the sum of
the underlying maps. -/
instance : Add (M₁.Hom M₂) :=
  ⟨fun f g => ⟨f.toLinearMap + g.toLinearMap,
    fun x => by rw [LinearMap.add_apply, LinearMap.add_apply, f.map_φ, g.map_φ, map_add],
    fun x => by rw [LinearMap.add_apply, LinearMap.add_apply, f.map_N, g.map_N, map_add]⟩⟩

/-- The negative of a morphism `f : M₁ → M₂` of `(φ, N)`-modules, whose underlying map is
`-f`. -/
instance : Neg (M₁.Hom M₂) :=
  ⟨fun f => ⟨-f.toLinearMap,
    fun x => by rw [LinearMap.neg_apply, LinearMap.neg_apply, f.map_φ, map_neg],
    fun x => by rw [LinearMap.neg_apply, LinearMap.neg_apply, f.map_N, map_neg]⟩⟩

/-- The difference of two morphisms `M₁ → M₂` of `(φ, N)`-modules, whose underlying map is the
difference of the underlying maps. -/
instance : Sub (M₁.Hom M₂) :=
  ⟨fun f g => ⟨f.toLinearMap - g.toLinearMap,
    fun x => by rw [LinearMap.sub_apply, LinearMap.sub_apply, f.map_φ, g.map_φ, map_sub],
    fun x => by rw [LinearMap.sub_apply, LinearMap.sub_apply, f.map_N, g.map_N, map_sub]⟩⟩

/-- The multiple `n • f` of a morphism `f : M₁ → M₂` of `(φ, N)`-modules by a natural number
`n`, whose underlying map is `n • f`. -/
instance : SMul ℕ (M₁.Hom M₂) :=
  ⟨fun n f => ⟨n • f.toLinearMap,
    fun x => by rw [LinearMap.smul_apply, LinearMap.smul_apply, f.map_φ, map_nsmul],
    fun x => by rw [LinearMap.smul_apply, LinearMap.smul_apply, f.map_N, map_nsmul]⟩⟩

/-- The multiple `n • f` of a morphism `f : M₁ → M₂` of `(φ, N)`-modules by an integer `n`,
whose underlying map is `n • f`. -/
instance : SMul ℤ (M₁.Hom M₂) :=
  ⟨fun n f => ⟨n • f.toLinearMap,
    fun x => by rw [LinearMap.smul_apply, LinearMap.smul_apply, f.map_φ, map_zsmul],
    fun x => by rw [LinearMap.smul_apply, LinearMap.smul_apply, f.map_N, map_zsmul]⟩⟩

/-- The `K₀`-linear map underlying the zero morphism `M₁ → M₂` is `0`. -/
@[simp]
theorem zero_toLinearMap : (0 : M₁.Hom M₂).toLinearMap = 0 :=
  rfl

/-- The `K₀`-linear map underlying `f + g` is the sum of those underlying `f` and `g`. -/
@[simp]
theorem add_toLinearMap (f g : M₁.Hom M₂) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap :=
  rfl

/-- The `K₀`-linear map underlying `-f` is the negative of that underlying `f`. -/
@[simp]
theorem neg_toLinearMap (f : M₁.Hom M₂) : (-f).toLinearMap = -f.toLinearMap :=
  rfl

/-- The `K₀`-linear map underlying `f - g` is the difference of those underlying `f` and `g`. -/
@[simp]
theorem sub_toLinearMap (f g : M₁.Hom M₂) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap :=
  rfl

/-- The `K₀`-linear map underlying `n • f`, for a natural number `n`, is `n • f.toLinearMap`. -/
@[simp]
theorem nsmul_toLinearMap (n : ℕ) (f : M₁.Hom M₂) : (n • f).toLinearMap = n • f.toLinearMap :=
  rfl

/-- The `K₀`-linear map underlying `n • f`, for an integer `n`, is `n • f.toLinearMap`. -/
@[simp]
theorem zsmul_toLinearMap (n : ℤ) (f : M₁.Hom M₂) : (n • f).toLinearMap = n • f.toLinearMap :=
  rfl

/-- The morphisms `M₁ → M₂` of `(φ, N)`-modules form an additive commutative group, with the
operations of the underlying `K₀`-linear maps. -/
instance : AddCommGroup (M₁.Hom M₂) :=
  toLinearMap_injective.addCommGroup _ zero_toLinearMap add_toLinearMap neg_toLinearMap
    sub_toLinearMap (fun _ _ => nsmul_toLinearMap _ _) fun _ _ => zsmul_toLinearMap _ _

/-- Composition of morphisms of `(φ, N)`-modules is additive in the first factor:
`(g₁ + g₂) ∘ f = g₁ ∘ f + g₂ ∘ f`. -/
theorem add_comp (g₁ g₂ : M₂.Hom M₃) (f : M₁.Hom M₂) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
  ext <| by simp only [comp_toLinearMap, add_toLinearMap, LinearMap.add_comp]

/-- Composition of morphisms of `(φ, N)`-modules is additive in the second factor:
`g ∘ (f₁ + f₂) = g ∘ f₁ + g ∘ f₂`. -/
theorem comp_add (g : M₂.Hom M₃) (f₁ f₂ : M₁.Hom M₂) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
  ext <| by simp only [comp_toLinearMap, add_toLinearMap, LinearMap.comp_add]

/-! ### Scalars fixed by `σ` -/

section Module

variable {R : Type*} [CommSemiring R] [Algebra R K₀]
  [hR : Fact (∀ r : R, σ (algebraMap R K₀ r) = algebraMap R K₀ r)]

/-- For a commutative semiring `R` and an `R`-algebra structure on `K₀` such that `σ` fixes
`algebraMap R K₀ r` for every `r : R` (a `Fact`), the multiple `r • f` of a morphism
`f : M₁ → M₂` of `(φ, N)`-modules, whose underlying map is `algebraMap R K₀ r • f`. -/
instance : SMul R (M₁.Hom M₂) :=
  ⟨fun r f => ⟨algebraMap R K₀ r • f.toLinearMap,
    fun x => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, f.map_φ, LinearEquiv.map_smulₛₗ, hR.out],
    fun x => by rw [LinearMap.smul_apply, LinearMap.smul_apply, f.map_N, map_smul]⟩⟩

/-- For an `R`-algebra structure on `K₀` such that `σ` fixes `algebraMap R K₀ r` for every
`r : R` (a `Fact`), the `K₀`-linear map underlying `r • f` is
`algebraMap R K₀ r • f.toLinearMap`. -/
@[simp]
theorem smul_toLinearMap (r : R) (f : M₁.Hom M₂) :
    (r • f).toLinearMap = algebraMap R K₀ r • f.toLinearMap :=
  rfl

/-- For a commutative semiring `R` and an `R`-algebra structure on `K₀` such that `σ` fixes
`algebraMap R K₀ r` for every `r : R` (a `Fact`), the morphisms `M₁ → M₂` of `(φ, N)`-modules
form an `R`-module. -/
instance : Module R (M₁.Hom M₂) :=
  letI : Module R (D₁ →ₗ[K₀] D₂) := Module.compHom _ (algebraMap R K₀)
  toLinearMap_injective.module R ⟨⟨toLinearMap, zero_toLinearMap⟩, add_toLinearMap⟩
    smul_toLinearMap

/-- For an `R`-algebra structure on `K₀` such that `σ` fixes `algebraMap R K₀ r` for every
`r : R` (a `Fact`), composition of morphisms of `(φ, N)`-modules is `R`-linear in the first
factor. -/
theorem smul_comp (r : R) (g : M₂.Hom M₃) (f : M₁.Hom M₂) : (r • g).comp f = r • g.comp f :=
  ext <| by simp only [comp_toLinearMap, smul_toLinearMap, LinearMap.smul_comp]

/-- For an `R`-algebra structure on `K₀` such that `σ` fixes `algebraMap R K₀ r` for every
`r : R` (a `Fact`), composition of morphisms of `(φ, N)`-modules is `R`-linear in the second
factor. -/
theorem comp_smul (r : R) (g : M₂.Hom M₃) (f : M₁.Hom M₂) : g.comp (r • f) = r • g.comp f :=
  ext <| by simp only [comp_toLinearMap, smul_toLinearMap, LinearMap.comp_smul]

end Module

end Hom

end PhiNModule

namespace FilteredPhiNModule

open TensorProduct

variable {K₀ : Type*} [Field K₀] {σ σ' : K₀ →+* K₀} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {p : K₀} {K : Type*} [Field K] [Algebra K₀ K] {D D₁ D₂ D₃ D₄ : Type*} [AddCommGroup D]
  [Module K₀ D] [AddCommGroup D₁] [Module K₀ D₁] [AddCommGroup D₂] [Module K₀ D₂]
  [AddCommGroup D₃] [Module K₀ D₃] [AddCommGroup D₄] [Module K₀ D₄]
  {M₁ : FilteredPhiNModule σ p K D₁} {M₂ : FilteredPhiNModule σ p K D₂}
  {M₃ : FilteredPhiNModule σ p K D₃} {M₄ : FilteredPhiNModule σ p K D₄}

/-- If the extension of scalars of `η` maps a `K`-subspace `S` of `D₁_K` into a `K`-subspace `T`
of `D₂_K`, then so does that of `c • η` for `c ∈ K₀`. -/
private theorem map_baseChange_smul_le {S : Submodule K (K ⊗[K₀] D₁)}
    {T : Submodule K (K ⊗[K₀] D₂)} (c : K₀) {η : D₁ →ₗ[K₀] D₂}
    (h : S.map (η.baseChange K) ≤ T) : S.map ((c • η).baseChange K) ≤ T := by
  rw [LinearMap.baseChange_smul]
  rintro - ⟨y, hy, rfl⟩
  exact Submodule.smul_of_tower_mem T c (h ⟨y, hy, rfl⟩)

namespace Hom

/-- Two morphisms of filtered `(φ, N)`-modules `M₁ → M₂` with the same underlying `K₀`-linear
map are equal. -/
@[ext]
theorem ext {f g : M₁.Hom M₂} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  obtain rfl : f = g := PhiNModule.Hom.ext h
  rfl

/-- A morphism of filtered `(φ, N)`-modules `M₁ → M₂` is determined by its underlying morphism
of `(φ, N)`-modules. -/
theorem toHom_injective :
    Function.Injective (toHom : M₁.Hom M₂ → M₁.toPhiNModule.Hom M₂.toPhiNModule) :=
  fun _ _ h => ext (congrArg PhiNModule.Hom.toLinearMap h)

variable (M₁) in
/-- The identity morphism of a filtered `(φ, N)`-module `M₁`, whose underlying map is the
identity. -/
def id : M₁.Hom M₁ where
  toHom := PhiNModule.Hom.id M₁.toPhiNModule
  map_fil_le i := le_of_eq (by
    rw [PhiNModule.Hom.id_toLinearMap, LinearMap.baseChange_id, Submodule.map_id])

variable (M₁) in
/-- The morphism of `(φ, N)`-modules underlying the identity of `M₁` is the identity. -/
@[simp]
theorem id_toHom : (id M₁).toHom = PhiNModule.Hom.id M₁.toPhiNModule :=
  rfl

/-- The composition `g ∘ f` of morphisms of filtered `(φ, N)`-modules `f : M₁ → M₂` and
`g : M₂ → M₃`, whose underlying map is the composition of the underlying maps. -/
def comp (g : M₂.Hom M₃) (f : M₁.Hom M₂) : M₁.Hom M₃ where
  toHom := g.toHom.comp f.toHom
  map_fil_le i := by
    rw [PhiNModule.Hom.comp_toLinearMap, LinearMap.baseChange_comp, Submodule.map_comp]
    exact (Submodule.map_mono (f.map_fil_le i)).trans (g.map_fil_le i)

/-- The morphism of `(φ, N)`-modules underlying `g.comp f` is `g.toHom.comp f.toHom`. -/
@[simp]
theorem comp_toHom (g : M₂.Hom M₃) (f : M₁.Hom M₂) : (g.comp f).toHom = g.toHom.comp f.toHom :=
  rfl

/-- Composing a morphism `f : M₁ → M₂` with the identity of `M₂` gives `f`. -/
@[simp]
theorem id_comp (f : M₁.Hom M₂) : (id M₂).comp f = f :=
  rfl

/-- Composing the identity of `M₁` with a morphism `f : M₁ → M₂` gives `f`. -/
@[simp]
theorem comp_id (f : M₁.Hom M₂) : f.comp (id M₁) = f :=
  rfl

/-- Composition of morphisms of filtered `(φ, N)`-modules is associative. -/
theorem comp_assoc (h : M₃.Hom M₄) (g : M₂.Hom M₃) (f : M₁.Hom M₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/-! ### The additive group of morphisms -/

/-- The zero morphism `M₁ → M₂` of filtered `(φ, N)`-modules. -/
instance : Zero (M₁.Hom M₂) :=
  ⟨⟨0, fun _ => by
    rw [PhiNModule.Hom.zero_toLinearMap, LinearMap.baseChange_zero, Submodule.map_zero]
    exact bot_le⟩⟩

/-- The sum of two morphisms `M₁ → M₂` of filtered `(φ, N)`-modules. -/
instance : Add (M₁.Hom M₂) :=
  ⟨fun f g => ⟨f.toHom + g.toHom, fun i => by
    rw [PhiNModule.Hom.add_toLinearMap, LinearMap.baseChange_add]
    exact (Submodule.map_add_le _ _ _).trans (sup_le (f.map_fil_le i) (g.map_fil_le i))⟩⟩

/-- The negative of a morphism `M₁ → M₂` of filtered `(φ, N)`-modules. -/
instance : Neg (M₁.Hom M₂) :=
  ⟨fun f => ⟨-f.toHom, fun i => by
    rw [PhiNModule.Hom.neg_toLinearMap, LinearMap.baseChange_neg, Submodule.map_neg]
    exact f.map_fil_le i⟩⟩

/-- The difference of two morphisms `M₁ → M₂` of filtered `(φ, N)`-modules. -/
instance : Sub (M₁.Hom M₂) :=
  ⟨fun f g => ⟨f.toHom - g.toHom, fun i => by
    rw [PhiNModule.Hom.sub_toLinearMap, LinearMap.baseChange_sub]
    rintro - ⟨y, hy, rfl⟩
    exact sub_mem (f.map_fil_le i ⟨y, hy, rfl⟩) (g.map_fil_le i ⟨y, hy, rfl⟩)⟩⟩

/-- The multiple `n • f` of a morphism `f : M₁ → M₂` of filtered `(φ, N)`-modules by a natural
number `n`. -/
instance : SMul ℕ (M₁.Hom M₂) :=
  ⟨fun n f => ⟨n • f.toHom, fun i => by
    rw [PhiNModule.Hom.nsmul_toLinearMap, ← Nat.cast_smul_eq_nsmul K₀]
    exact map_baseChange_smul_le _ (f.map_fil_le i)⟩⟩

/-- The multiple `n • f` of a morphism `f : M₁ → M₂` of filtered `(φ, N)`-modules by an integer
`n`. -/
instance : SMul ℤ (M₁.Hom M₂) :=
  ⟨fun n f => ⟨n • f.toHom, fun i => by
    rw [PhiNModule.Hom.zsmul_toLinearMap, ← Int.cast_smul_eq_zsmul K₀]
    exact map_baseChange_smul_le _ (f.map_fil_le i)⟩⟩

/-- The morphism of `(φ, N)`-modules underlying the zero morphism is `0`. -/
@[simp]
theorem zero_toHom : (0 : M₁.Hom M₂).toHom = 0 :=
  rfl

/-- The morphism of `(φ, N)`-modules underlying `f + g` is `f.toHom + g.toHom`. -/
@[simp]
theorem add_toHom (f g : M₁.Hom M₂) : (f + g).toHom = f.toHom + g.toHom :=
  rfl

/-- The morphism of `(φ, N)`-modules underlying `-f` is `-f.toHom`. -/
@[simp]
theorem neg_toHom (f : M₁.Hom M₂) : (-f).toHom = -f.toHom :=
  rfl

/-- The morphism of `(φ, N)`-modules underlying `f - g` is `f.toHom - g.toHom`. -/
@[simp]
theorem sub_toHom (f g : M₁.Hom M₂) : (f - g).toHom = f.toHom - g.toHom :=
  rfl

/-- The morphism of `(φ, N)`-modules underlying `n • f`, for `n : ℕ`, is `n • f.toHom`. -/
@[simp]
theorem nsmul_toHom (n : ℕ) (f : M₁.Hom M₂) : (n • f).toHom = n • f.toHom :=
  rfl

/-- The morphism of `(φ, N)`-modules underlying `n • f`, for `n : ℤ`, is `n • f.toHom`. -/
@[simp]
theorem zsmul_toHom (n : ℤ) (f : M₁.Hom M₂) : (n • f).toHom = n • f.toHom :=
  rfl

/-- The morphisms `M₁ → M₂` of filtered `(φ, N)`-modules form an additive commutative group,
with the operations of the underlying `K₀`-linear maps. -/
instance : AddCommGroup (M₁.Hom M₂) :=
  toHom_injective.addCommGroup _ zero_toHom add_toHom neg_toHom sub_toHom
    (fun _ _ => nsmul_toHom _ _) fun _ _ => zsmul_toHom _ _

/-- Composition of morphisms of filtered `(φ, N)`-modules is additive in the first factor. -/
theorem add_comp (g₁ g₂ : M₂.Hom M₃) (f : M₁.Hom M₂) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
  toHom_injective (PhiNModule.Hom.add_comp _ _ _)

/-- Composition of morphisms of filtered `(φ, N)`-modules is additive in the second factor. -/
theorem comp_add (g : M₂.Hom M₃) (f₁ f₂ : M₁.Hom M₂) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
  toHom_injective (PhiNModule.Hom.comp_add _ _ _)

section Module

variable {R : Type*} [CommSemiring R] [Algebra R K₀]
  [Fact (∀ r : R, σ (algebraMap R K₀ r) = algebraMap R K₀ r)]

/-- For a commutative semiring `R` and an `R`-algebra structure on `K₀` such that `σ` fixes
`algebraMap R K₀ r` for every `r : R` (a `Fact`), the multiple `r • f` of a morphism
`f : M₁ → M₂` of filtered `(φ, N)`-modules, whose underlying map is `algebraMap R K₀ r • f`. -/
instance : SMul R (M₁.Hom M₂) :=
  ⟨fun r f => ⟨r • f.toHom, fun i => by
    rw [PhiNModule.Hom.smul_toLinearMap]
    exact map_baseChange_smul_le _ (f.map_fil_le i)⟩⟩

/-- For an `R`-algebra structure on `K₀` such that `σ` fixes `algebraMap R K₀ r` for every
`r : R` (a `Fact`), the morphism of `(φ, N)`-modules underlying `r • f` is `r • f.toHom`. -/
@[simp]
theorem smul_toHom (r : R) (f : M₁.Hom M₂) : (r • f).toHom = r • f.toHom :=
  rfl

/-- For a commutative semiring `R` and an `R`-algebra structure on `K₀` such that `σ` fixes
`algebraMap R K₀ r` for every `r : R` (a `Fact`), the morphisms `M₁ → M₂` of filtered
`(φ, N)`-modules form an `R`-module. -/
instance : Module R (M₁.Hom M₂) :=
  toHom_injective.module R ⟨⟨toHom, zero_toHom⟩, add_toHom⟩ smul_toHom

/-- For an `R`-algebra structure on `K₀` such that `σ` fixes `algebraMap R K₀ r` for every
`r : R` (a `Fact`), composition of morphisms of filtered `(φ, N)`-modules is `R`-linear in the
first factor. -/
theorem smul_comp (r : R) (g : M₂.Hom M₃) (f : M₁.Hom M₂) : (r • g).comp f = r • g.comp f :=
  toHom_injective (PhiNModule.Hom.smul_comp _ _ _)

/-- For an `R`-algebra structure on `K₀` such that `σ` fixes `algebraMap R K₀ r` for every
`r : R` (a `Fact`), composition of morphisms of filtered `(φ, N)`-modules is `R`-linear in the
second factor. -/
theorem comp_smul (r : R) (g : M₂.Hom M₃) (f : M₁.Hom M₂) : g.comp (r • f) = r • g.comp f :=
  toHom_injective (PhiNModule.Hom.comp_smul _ _ _)

end Module

end Hom

/-! ### Inclusions of stable subspaces, quotient maps and images -/

variable (M : FilteredPhiNModule σ p K D) [FiniteDimensional K₀ D]

/-- The inclusion of a stable subspace `D'` of a finite-dimensional filtered `(φ, N)`-module `D`,
with the induced filtration (`FilteredPhiNModule.restrict`), as a morphism into `D`. -/
def subtype (D' : Submodule K₀ D) (h : M.IsStable D') : (M.restrict D' h).Hom M where
  toLinearMap := D'.subtype
  map_φ _ := rfl
  map_N _ := rfl
  map_fil_le _ := Submodule.map_comap_le _ _

/-- The linear map underlying `M.subtype D' h` is `D'.subtype`. -/
@[simp]
theorem subtype_toLinearMap (D' : Submodule K₀ D) (h : M.IsStable D') :
    (M.subtype D' h).toLinearMap = D'.subtype :=
  rfl

/-- The projection of a finite-dimensional filtered `(φ, N)`-module `D` onto its quotient by a
stable subspace `D'`, with the quotient filtration (`FilteredPhiNModule.quotient`), as a
morphism. -/
def mkQ (D' : Submodule K₀ D) (h : M.IsStable D') : M.Hom (M.quotient D' h) where
  toLinearMap := D'.mkQ
  map_φ _ := rfl
  map_N _ := rfl
  map_fil_le _ := le_rfl

/-- The linear map underlying `M.mkQ D' h` is `D'.mkQ`. -/
@[simp]
theorem mkQ_toLinearMap (D' : Submodule K₀ D) (h : M.IsStable D') :
    (M.mkQ D' h).toLinearMap = D'.mkQ :=
  rfl

variable {M} [FiniteDimensional K₀ D₂]

/-- The corestriction `D₁ → Im η` of a morphism `η : M₁ → M₂` of filtered `(φ, N)`-modules, with
`D₂` finite-dimensional, to its image with the filtration induced from `D₂_K`
(`FilteredPhiNModule.restrict`): its extension of scalars maps `Fil^i D₁_K` into the induced
filtration because `η_K` maps it into `Fil^i D₂_K`. -/
def Hom.rangeRestrict (η : M₁.Hom M₂) :
    M₁.Hom (M₂.restrict (LinearMap.range η.toLinearMap) η.isStable_range) where
  toLinearMap := η.toLinearMap.rangeRestrict
  map_φ x := Subtype.ext (η.map_φ x)
  map_N x := Subtype.ext (η.map_N x)
  map_fil_le i := by
    rw [restrict_fil_fil, Submodule.map_le_iff_le_comap, ← Submodule.comap_comp,
      ← LinearMap.baseChange_comp, LinearMap.subtype_comp_codRestrict,
      ← Submodule.map_le_iff_le_comap]
    exact η.map_fil_le i

/-- The linear map underlying `η.rangeRestrict` is `η.toLinearMap.rangeRestrict`. -/
@[simp]
theorem Hom.rangeRestrict_toLinearMap (η : M₁.Hom M₂) :
    η.rangeRestrict.toLinearMap = η.toLinearMap.rangeRestrict :=
  rfl

/-- A morphism `η` of filtered `(φ, N)`-modules, with finite-dimensional target, is the
composition of its corestriction to its image and the inclusion of the image. -/
theorem Hom.subtype_comp_rangeRestrict (η : M₁.Hom M₂) :
    (M₂.subtype _ η.isStable_range).comp η.rangeRestrict = η :=
  ext (LinearMap.subtype_comp_codRestrict _ _ _)

end FilteredPhiNModule
