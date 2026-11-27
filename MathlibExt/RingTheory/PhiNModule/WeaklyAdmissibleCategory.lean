/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.PhiNModule.Hom
public import MathlibExt.RingTheory.PhiNModule.Prod
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The abelian category of weakly admissible filtered `(φ, N)`-modules

Let `K₀` be a field with a ring automorphism `σ` (given with its inverse `σ'`), let `p ∈ K₀`, let
`K` be a field extension of `K₀` and let `v : AddValuation K₀ (WithTop ℤ)` be an additive
valuation. The finite-dimensional filtered `(φ, N)`-modules over `K` that are weakly admissible
for `v`, with the morphisms of filtered `(φ, N)`-modules, form a category
`FilteredPhiNModule.WeaklyAdmissibleCat σ p K v`. It is preadditive, and `R`-linear for every
`R`-algebra structure on `K₀` such that `σ` fixes the image of `R` (`ℚ_p` in the setting of
Fontaine–Ouyang). Morphisms are not stable under multiplication by all scalars of `K₀`, as `φ`
is `σ`-semilinear.

If `v ∘ σ = v` (assumed as a `Fact`), the category is abelian (Fontaine–Ouyang,
Proposition 8.41; Fontaine, Exposé III, §4.4.4): the kernel of a morphism `f : X ⟶ Y` is
`Ker f` with the filtration induced from `X`, its cokernel is `Y ⧸ Im f` with the quotient
filtration, and its image `Im f` with the filtration induced from `Y` is also the cokernel of the
inclusion of `Ker f`, as the filtration induced from `Y` is the quotient filtration from `X` by
the strictness of `f` (`FilteredPhiNModule.IsWeaklyAdmissible.map_fil_eq_range_inf_fil`). The
forgetful functor to `K₀`-vector spaces is faithful, additive and exact, and reflects
isomorphisms.

## Main definitions

* `FilteredPhiNModule.WeaklyAdmissibleCat σ p K v`: the category.
* `FilteredPhiNModule.WeaklyAdmissibleCat.kernelFork`,
  `FilteredPhiNModule.WeaklyAdmissibleCat.cokernelCofork`: the kernel and the cokernel of a
  morphism, with `kernelIsLimit` and `cokernelIsColimit`.
* `FilteredPhiNModule.WeaklyAdmissibleCat.forgetToModuleCat`: the forgetful functor to
  `ModuleCat K₀`.

## Main results

* `FilteredPhiNModule.WeaklyAdmissibleCat.instPreadditive`,
  `FilteredPhiNModule.WeaklyAdmissibleCat.instLinear`: the category is preadditive, and
  `R`-linear when `σ` fixes the image of `R` in `K₀`.
* `FilteredPhiNModule.WeaklyAdmissibleCat.instAbelian`: for `v ∘ σ = v`, the category is abelian.
* `FilteredPhiNModule.IsWeaklyAdmissible.restrict_range_fil_fil`: the filtration of the image of
  a morphism of weakly admissible modules induced from the target is the quotient filtration
  from the source.
* Instances stating that `forgetToModuleCat` is faithful and additive and, for `v ∘ σ = v`,
  preserves finite limits and finite colimits and reflects isomorphisms.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.3 and §8.2.5: Definition 8.34, Exercise 8.35, Definition 8.39 and Proposition 8.41.
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.3.3 pp. 148–149 and §4.4.3–§4.4.4 p. 151.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Module TensorProduct

universe u

namespace FilteredPhiNModule

variable {K₀ : Type*} [Field K₀] {σ σ' : K₀ →+* K₀} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {p : K₀} {K : Type*} [Field K] [Algebra K₀ K] {v : AddValuation K₀ (WithTop ℤ)}

/-! ### The zero module and the strictness of morphisms -/

variable (σ p K) in
/-- The filtered `(φ, N)`-module structure on the zero space `PUnit`: `φ` is the identity, `N = 0`
and the filtration of `K ⊗_{K₀} PUnit` jumps at `0`. -/
def punit : FilteredPhiNModule σ p K PUnit where
  φ :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  N := 0
  N_φ _ := rfl
  fil := DecreasingFiltration.single 0

/-- A filtered `(φ, N)`-module on a zero space `D` (a subsingleton, finite-dimensional over `K₀`)
is weakly admissible for every additive valuation `v`: `t_H` and `t_N` vanish on `D` and on its
subspaces. -/
theorem isWeaklyAdmissible_of_subsingleton {D : Type*} [AddCommGroup D] [Module K₀ D]
    [FiniteDimensional K₀ D] [Subsingleton D] (M : FilteredPhiNModule σ p K D) :
    M.IsWeaklyAdmissible v where
  hodgeNumber_eq_newtonNumber := by
    rw [M.hodgeNumber_eq_zero_of_finrank_eq_zero finrank_zero_of_subsingleton,
      PhiNModule.newtonNumber_eq_zero_of_finrank_eq_zero v _ finrank_zero_of_subsingleton]
  hodgeNumber_restrict_le D' h := by
    rw [hodgeNumber_eq_zero_of_finrank_eq_zero _ finrank_zero_of_subsingleton,
      PhiNModule.newtonNumber_eq_zero_of_finrank_eq_zero v _ finrank_zero_of_subsingleton]

/-- Extension of scalars along `K₀ → K` preserves injectivity. -/
private theorem baseChange_injective' {V W : Type*} [AddCommGroup V] [Module K₀ V]
    [AddCommGroup W] [Module K₀ W] {f : V →ₗ[K₀] W} (hf : Function.Injective f) :
    Function.Injective (f.baseChange K) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Extension of scalars along `K₀ → K` preserves surjectivity. -/
private theorem baseChange_surjective' {V W : Type*} [AddCommGroup V] [Module K₀ V]
    [AddCommGroup W] [Module K₀ W] {f : V →ₗ[K₀] W} (hf : Function.Surjective f) :
    Function.Surjective (f.baseChange K) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact LinearMap.lTensor_surjective K hf

/-- Fontaine–Ouyang, Proposition 8.41 (3), for the image (Fontaine, Exposé III, §4.3.3): let `v`
be an additive valuation with `v ∘ σ = v` and `η : M₁ → M₂` a morphism of finite-dimensional
filtered `(φ, N)`-modules that are weakly admissible for `v`. Then on `(Im η)_K` the filtration
induced from `D₂_K` is the quotient filtration from `D₁_K`: its `i`-th step is the image of
`Fil^i D₁_K` under the corestriction `D₁_K → (Im η)_K` of `η_K`. -/
theorem IsWeaklyAdmissible.restrict_range_fil_fil {D₁ D₂ : Type*} [AddCommGroup D₁]
    [Module K₀ D₁] [AddCommGroup D₂] [Module K₀ D₂] [FiniteDimensional K₀ D₁]
    [FiniteDimensional K₀ D₂] {M₁ : FilteredPhiNModule σ p K D₁}
    {M₂ : FilteredPhiNModule σ p K D₂} (hv : ∀ x, v (σ x) = v x) (h₁ : M₁.IsWeaklyAdmissible v)
    (h₂ : M₂.IsWeaklyAdmissible v) (η : M₁.Hom M₂) (i : ℤ) :
    (M₂.restrict (LinearMap.range η.toLinearMap) η.isStable_range).fil.Fil i =
      (M₁.fil.Fil i).map (η.toLinearMap.rangeRestrict.baseChange K) := by
  have hc : (LinearMap.range η.toLinearMap).subtype.baseChange K ∘ₗ
      η.toLinearMap.rangeRestrict.baseChange K = η.toLinearMap.baseChange K := by
    rw [← LinearMap.baseChange_comp, LinearMap.subtype_comp_codRestrict]
  apply Submodule.map_injective_of_injective (baseChange_injective' (K := K)
    (LinearMap.range η.toLinearMap).injective_subtype)
  rw [← Submodule.map_comp, hc, h₁.map_fil_eq_range_inf_fil hv h₂ η i, restrict_fil_fil,
    Submodule.map_comap_eq, ← hc, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (baseChange_surjective' η.toLinearMap.surjective_rangeRestrict))]

/-! ### The category -/

variable (σ p K v) in
/-- The category of finite-dimensional weakly admissible filtered `(φ, N)`-modules over `K`, for
a field `K₀` with a ring automorphism `σ` (with inverse `σ'`), a scalar `p ∈ K₀`, a field
extension `K` of `K₀` and an additive valuation `v : AddValuation K₀ (WithTop ℤ)`. An object is a
`K₀`-vector space `D` in the universe `u`, finite-dimensional over `K₀`, with a filtered
`(φ, N)`-module structure over `K` that is weakly admissible for `v`; the morphisms are the
morphisms of filtered `(φ, N)`-modules (`FilteredPhiNModule.Hom`). When `K` is a `p`-adic field,
`K₀ = W(k)[1/p]` is its maximal absolutely unramified subfield, `σ` is the absolute Frobenius and
`v` is the `p`-adic valuation (so `v ∘ σ = v`), this is the category `MF^ad_K(φ, N)` of
Fontaine–Ouyang, Definition 8.39 (who call these modules *admissible*), and the category of
Fontaine, Exposé III, §4.4.3, with `L = K`. -/
structure WeaklyAdmissibleCat where
  /-- The underlying `K₀`-vector space `D`. -/
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module K₀ carrier]
  [instFiniteDimensional : FiniteDimensional K₀ carrier]
  /-- The filtered `(φ, N)`-module structure on `D`. -/
  str : FilteredPhiNModule σ p K carrier
  /-- `D` is weakly admissible for `v`. -/
  isWeaklyAdmissible : str.IsWeaklyAdmissible v

namespace WeaklyAdmissibleCat

attribute [instance] instAddCommGroup instModule instFiniteDimensional

/-- An object of `WeaklyAdmissibleCat σ p K v` coerces to its underlying `K₀`-vector space. -/
instance : CoeSort (WeaklyAdmissibleCat.{u} σ p K v) (Type u) :=
  ⟨carrier⟩

/-- The object of `WeaklyAdmissibleCat σ p K v` given by a `K₀`-vector space `D`,
finite-dimensional over `K₀`, with a filtered `(φ, N)`-module structure `M` over `K` that is
weakly admissible for `v`. -/
abbrev of (D : Type u) [AddCommGroup D] [Module K₀ D] [FiniteDimensional K₀ D]
    (M : FilteredPhiNModule σ p K D) (hM : M.IsWeaklyAdmissible v) :
    WeaklyAdmissibleCat.{u} σ p K v :=
  ⟨D, M, hM⟩

/-- The category structure on `WeaklyAdmissibleCat σ p K v`: the morphisms `X ⟶ Y` are the
morphisms of filtered `(φ, N)`-modules, with the identity maps and the composition of maps. -/
instance : Category.{u} (WeaklyAdmissibleCat.{u} σ p K v) where
  Hom X Y := X.str.Hom Y.str
  id X := Hom.id X.str
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {X Y Z : WeaklyAdmissibleCat.{u} σ p K v}

/-- Two morphisms `X ⟶ Y` in `WeaklyAdmissibleCat σ p K v` with the same underlying `K₀`-linear
map are equal. -/
@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.toLinearMap = g.toLinearMap) : f = g :=
  Hom.ext h

/-- Equal morphisms have equal underlying `K₀`-linear maps. -/
theorem congr_toLinearMap {f g : X ⟶ Y} (h : f = g) : f.toLinearMap = g.toLinearMap := by
  rw [h]

/-- The `K₀`-linear map underlying the identity of `X` is the identity. -/
@[simp]
theorem id_toLinearMap (X : WeaklyAdmissibleCat.{u} σ p K v) :
    (𝟙 X : X ⟶ X).toLinearMap = LinearMap.id :=
  rfl

/-- The `K₀`-linear map underlying `f ≫ g` is `g ∘ₗ f`. -/
@[simp]
theorem comp_toLinearMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  rfl

/-- `WeaklyAdmissibleCat σ p K v` is preadditive: the morphisms `X ⟶ Y` form an additive
commutative group, with the operations of the underlying `K₀`-linear maps, and composition is
biadditive. -/
instance instPreadditive : Preadditive (WeaklyAdmissibleCat.{u} σ p K v) where
  homGroup X Y := inferInstanceAs (AddCommGroup (X.str.Hom Y.str))
  add_comp _ _ _ f f' g := Hom.comp_add g f f'
  comp_add _ _ _ f g g' := Hom.add_comp g g' f

/-- The `K₀`-linear map underlying the zero morphism `X ⟶ Y` is `0`. -/
@[simp]
theorem zero_toLinearMap : (0 : X ⟶ Y).toLinearMap = 0 :=
  rfl

/-- The `K₀`-linear map underlying `f + g` is the sum of those underlying `f` and `g`. -/
@[simp]
theorem add_toLinearMap (f g : X ⟶ Y) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap :=
  rfl

/-- The `K₀`-linear map underlying `-f` is the negative of that underlying `f`. -/
@[simp]
theorem neg_toLinearMap (f : X ⟶ Y) : (-f).toLinearMap = -f.toLinearMap :=
  rfl

/-- The `K₀`-linear map underlying `f - g` is the difference of those underlying `f` and `g`. -/
@[simp]
theorem sub_toLinearMap (f g : X ⟶ Y) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap :=
  rfl

section Linear

variable {R : Type*} [CommSemiring R] [Algebra R K₀]
  [Fact (∀ r : R, σ (algebraMap R K₀ r) = algebraMap R K₀ r)]

/-- For a commutative semiring `R` and an `R`-algebra structure on `K₀` such that `σ` fixes
`algebraMap R K₀ r` for every `r : R` (a `Fact`), `WeaklyAdmissibleCat σ p K v` is `R`-linear:
`r • f` has underlying map `algebraMap R K₀ r • f`, and composition is `R`-bilinear. In the
setting of Fontaine–Ouyang one can take `R = ℚ_p` (Fontaine, Exposé III, §4.3.3). -/
instance instLinear : Linear R (WeaklyAdmissibleCat.{u} σ p K v) where
  homModule X Y := inferInstanceAs (Module R (X.str.Hom Y.str))
  smul_comp _ _ _ r f g := Hom.comp_smul r g f
  comp_smul _ _ _ f r g := Hom.smul_comp r g f

/-- For an `R`-algebra structure on `K₀` such that `σ` fixes `algebraMap R K₀ r` for every
`r : R` (a `Fact`), the `K₀`-linear map underlying `r • f` is `algebraMap R K₀ r • f`. -/
@[simp]
theorem smul_toLinearMap (r : R) (f : X ⟶ Y) :
    (r • f).toLinearMap = algebraMap R K₀ r • f.toLinearMap :=
  rfl

end Linear

/-! ### The zero object -/

/-- An object of `WeaklyAdmissibleCat σ p K v` whose underlying `K₀`-vector space is a
subsingleton (the zero space) is a zero object. -/
theorem isZero_of_subsingleton (X : WeaklyAdmissibleCat.{u} σ p K v) [Subsingleton X] :
    IsZero X :=
  IsZero.mk (fun _ => ⟨⟨⟨0⟩, fun f => hom_ext <| LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩)
    fun _ => ⟨⟨⟨0⟩, fun _ => hom_ext <| LinearMap.ext fun _ => Subsingleton.elim _ _⟩⟩

/-- `WeaklyAdmissibleCat σ p K v` has a zero object, the zero space `PUnit`
(`FilteredPhiNModule.punit`). -/
instance : HasZeroObject (WeaklyAdmissibleCat.{u} σ p K v) :=
  ⟨⟨of PUnit (punit σ p K) (isWeaklyAdmissible_of_subsingleton _), isZero_of_subsingleton _⟩⟩

/-! ### Kernels and cokernels from linear algebra -/

section Criteria

variable {W Q T : WeaklyAdmissibleCat.{u} σ p K v}

/-- If `g ≫ f = 0` and the kernel of the map underlying `f` is contained in the image of the
map underlying `ι`, then the image of the map underlying `g` is contained in that of `ι`. -/
theorem range_le_of_comp_eq_zero {f : X ⟶ Y} {ι : W ⟶ X} {g : T ⟶ X} (hg : g ≫ f = 0)
    (hker : LinearMap.ker f.toLinearMap ≤ LinearMap.range ι.toLinearMap) :
    LinearMap.range g.toLinearMap ≤ LinearMap.range ι.toLinearMap :=
  (LinearMap.range_le_ker_iff.mpr
    (show f.toLinearMap ∘ₗ g.toLinearMap = 0 from congr_toLinearMap hg)).trans hker

/-- If `f ≫ g = 0` and the kernel of the map underlying `π` is contained in the image of the
map underlying `f`, then the kernel of the map underlying `π` is contained in that of `g`. -/
theorem ker_le_of_comp_eq_zero {f : X ⟶ Y} {π : Y ⟶ Q} {g : Y ⟶ T} (hg : f ≫ g = 0)
    (hker : LinearMap.ker π.toLinearMap ≤ LinearMap.range f.toLinearMap) :
    LinearMap.ker π.toLinearMap ≤ LinearMap.ker g.toLinearMap :=
  hker.trans (LinearMap.range_le_ker_iff.mpr
    (show g.toLinearMap ∘ₗ f.toLinearMap = 0 from congr_toLinearMap hg))

/-- For morphisms `ι : W ⟶ X` with injective underlying map and `g : T ⟶ X` whose underlying map
has image contained in that of `ι`, the `K₀`-linear map `T → W` through which the map underlying
`g` factors along that of `ι`. -/
def liftLinearMap (ι : W ⟶ X) (hι : Function.Injective ι.toLinearMap) (g : T ⟶ X)
    (hg : LinearMap.range g.toLinearMap ≤ LinearMap.range ι.toLinearMap) : T →ₗ[K₀] W :=
  (LinearEquiv.ofInjective ι.toLinearMap hι).symm.toLinearMap ∘ₗ
    g.toLinearMap.codRestrict _ fun x => hg (LinearMap.mem_range_self _ x)

/-- For `ι : W ⟶ X` with injective underlying map and `g : T ⟶ X` whose image is contained in
that of `ι`, `ι` maps `liftLinearMap ι hι g hg x` to `g x`. -/
theorem apply_liftLinearMap (ι : W ⟶ X) (hι : Function.Injective ι.toLinearMap) (g : T ⟶ X)
    (hg : LinearMap.range g.toLinearMap ≤ LinearMap.range ι.toLinearMap) (x : T) :
    ι.toLinearMap (liftLinearMap ι hι g hg x) = g.toLinearMap x :=
  LinearEquiv.ofInjective_symm_apply (h := hι) _ _

/-- For `ι : W ⟶ X` with injective underlying map and `g : T ⟶ X` whose image is contained in
that of `ι`, the composition of `liftLinearMap ι hι g hg` with the map underlying `ι` is the map
underlying `g`. -/
theorem comp_liftLinearMap (ι : W ⟶ X) (hι : Function.Injective ι.toLinearMap) (g : T ⟶ X)
    (hg : LinearMap.range g.toLinearMap ≤ LinearMap.range ι.toLinearMap) :
    ι.toLinearMap ∘ₗ liftLinearMap ι hι g hg = g.toLinearMap :=
  LinearMap.ext (apply_liftLinearMap ι hι g hg)

/-- For a morphism `ι : W ⟶ X` with injective underlying map such that
`ι_K⁻¹(Fil^i X_K) ≤ Fil^i W_K` for every `i`, and a morphism `g : T ⟶ X` whose underlying map has
image contained in that of `ι`, the morphism `T ⟶ W` through which `g` factors along `ι`. -/
def liftOfInjective (ι : W ⟶ X) (hι : Function.Injective ι.toLinearMap)
    (hfil : ∀ i, (X.str.fil.Fil i).comap (ι.toLinearMap.baseChange K) ≤ W.str.fil.Fil i)
    (g : T ⟶ X) (hg : LinearMap.range g.toLinearMap ≤ LinearMap.range ι.toLinearMap) :
    T ⟶ W where
  toLinearMap := liftLinearMap ι hι g hg
  map_φ x := hι <| by
    rw [apply_liftLinearMap, ι.map_φ, apply_liftLinearMap, g.map_φ]
  map_N x := hι <| by
    rw [apply_liftLinearMap, ι.map_N, apply_liftLinearMap, g.map_N]
  map_fil_le i := by
    rintro - ⟨y, hy, rfl⟩
    refine hfil i ?_
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      comp_liftLinearMap]
    exact g.map_fil_le i ⟨y, hy, rfl⟩

/-- A criterion for kernels in `WeaklyAdmissibleCat σ p K v`: let `f : X ⟶ Y` and `ι : W ⟶ X`
with `ι ≫ f = 0`. If the underlying map of `ι` is injective, its image contains the kernel of
`f`, and `W` carries the filtration induced from `X` (`ι_K⁻¹(Fil^i X_K) ≤ Fil^i W_K` for every
`i`), then `ι` is a kernel of `f`. -/
def isLimitKernelFork {f : X ⟶ Y} (ι : W ⟶ X) (w : ι ≫ f = 0)
    (hι : Function.Injective ι.toLinearMap)
    (hker : LinearMap.ker f.toLinearMap ≤ LinearMap.range ι.toLinearMap)
    (hfil : ∀ i, (X.str.fil.Fil i).comap (ι.toLinearMap.baseChange K) ≤ W.str.fil.Fil i) :
    IsLimit (KernelFork.ofι ι w) :=
  KernelFork.IsLimit.ofι ι w
    (fun g hg => liftOfInjective ι hι hfil g (range_le_of_comp_eq_zero hg hker))
    (fun g hg => hom_ext (comp_liftLinearMap ι hι g (range_le_of_comp_eq_zero hg hker)))
    fun g hg _ hm => hom_ext <| LinearMap.ext fun x => hι <|
      (LinearMap.congr_fun (congr_toLinearMap hm) x).trans
        (apply_liftLinearMap ι hι g (range_le_of_comp_eq_zero hg hker) x).symm

/-- For morphisms `π : Y ⟶ Q` with surjective underlying map and `g : Y ⟶ T` whose underlying map
has kernel containing that of `π`, the `K₀`-linear map `Q → T` through which the map underlying
`g` factors along that of `π`. -/
def descLinearMap (π : Y ⟶ Q) (hπ : Function.Surjective π.toLinearMap) (g : Y ⟶ T)
    (hg : LinearMap.ker π.toLinearMap ≤ LinearMap.ker g.toLinearMap) : Q →ₗ[K₀] T :=
  (LinearMap.ker π.toLinearMap).liftQ g.toLinearMap hg ∘ₗ
    (π.toLinearMap.quotKerEquivOfSurjective hπ).symm.toLinearMap

/-- For `π : Y ⟶ Q` with surjective underlying map and `g : Y ⟶ T` whose kernel contains that
of `π`, `descLinearMap π hπ g hg` maps `π y` to `g y`. -/
theorem descLinearMap_apply (π : Y ⟶ Q) (hπ : Function.Surjective π.toLinearMap) (g : Y ⟶ T)
    (hg : LinearMap.ker π.toLinearMap ≤ LinearMap.ker g.toLinearMap) (y : Y) :
    descLinearMap π hπ g hg (π.toLinearMap y) = g.toLinearMap y := by
  have h : (π.toLinearMap.quotKerEquivOfSurjective hπ).symm (π.toLinearMap y) =
      Submodule.Quotient.mk y :=
    (LinearEquiv.symm_apply_eq _).mpr (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm
  rw [descLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]

/-- For `π : Y ⟶ Q` with surjective underlying map and `g : Y ⟶ T` whose kernel contains that
of `π`, the composition of the map underlying `π` with `descLinearMap π hπ g hg` is the map
underlying `g`. -/
theorem descLinearMap_comp (π : Y ⟶ Q) (hπ : Function.Surjective π.toLinearMap) (g : Y ⟶ T)
    (hg : LinearMap.ker π.toLinearMap ≤ LinearMap.ker g.toLinearMap) :
    descLinearMap π hπ g hg ∘ₗ π.toLinearMap = g.toLinearMap :=
  LinearMap.ext (descLinearMap_apply π hπ g hg)

/-- For a morphism `π : Y ⟶ Q` with surjective underlying map such that
`Fil^i Q_K ≤ π_K(Fil^i Y_K)` for every `i`, and a morphism `g : Y ⟶ T` whose underlying map has
kernel containing that of `π`, the morphism `Q ⟶ T` through which `g` factors along `π`. -/
def descOfSurjective (π : Y ⟶ Q) (hπ : Function.Surjective π.toLinearMap)
    (hfil : ∀ i, Q.str.fil.Fil i ≤ (Y.str.fil.Fil i).map (π.toLinearMap.baseChange K))
    (g : Y ⟶ T) (hg : LinearMap.ker π.toLinearMap ≤ LinearMap.ker g.toLinearMap) :
    Q ⟶ T where
  toLinearMap := descLinearMap π hπ g hg
  map_φ q := by
    obtain ⟨y, rfl⟩ := hπ q
    rw [← π.map_φ, descLinearMap_apply, descLinearMap_apply, g.map_φ]
  map_N q := by
    obtain ⟨y, rfl⟩ := hπ q
    rw [← π.map_N, descLinearMap_apply, descLinearMap_apply, g.map_N]
  map_fil_le i := by
    refine (Submodule.map_mono (hfil i)).trans ?_
    rw [← Submodule.map_comp, ← LinearMap.baseChange_comp, descLinearMap_comp]
    exact g.map_fil_le i

/-- A criterion for cokernels in `WeaklyAdmissibleCat σ p K v`: let `f : X ⟶ Y` and `π : Y ⟶ Q`
with `f ≫ π = 0`. If the underlying map of `π` is surjective, its kernel is contained in the
image of `f`, and `Q` carries the quotient filtration from `Y`
(`Fil^i Q_K ≤ π_K(Fil^i Y_K)` for every `i`), then `π` is a cokernel of `f`. -/
def isColimitCokernelCofork {f : X ⟶ Y} (π : Y ⟶ Q) (w : f ≫ π = 0)
    (hπ : Function.Surjective π.toLinearMap)
    (hker : LinearMap.ker π.toLinearMap ≤ LinearMap.range f.toLinearMap)
    (hfil : ∀ i, Q.str.fil.Fil i ≤ (Y.str.fil.Fil i).map (π.toLinearMap.baseChange K)) :
    IsColimit (CokernelCofork.ofπ π w) :=
  CokernelCofork.IsColimit.ofπ π w
    (fun g hg => descOfSurjective π hπ hfil g (ker_le_of_comp_eq_zero hg hker))
    (fun g hg => hom_ext (descLinearMap_comp π hπ g (ker_le_of_comp_eq_zero hg hker)))
    fun g hg m hm => hom_ext <| LinearMap.ext fun q => by
      obtain ⟨y, rfl⟩ := hπ q
      exact (LinearMap.congr_fun (congr_toLinearMap hm) y).trans
        (descLinearMap_apply π hπ g (ker_le_of_comp_eq_zero hg hker) y).symm

end Criteria

/-! ### The forgetful functor -/

variable (σ p K v) in
/-- The forgetful functor from `WeaklyAdmissibleCat σ p K v` to `K₀`-vector spaces, sending an
object to its underlying `K₀`-vector space and a morphism to its underlying `K₀`-linear map. -/
@[simps]
def forgetToModuleCat : WeaklyAdmissibleCat.{u} σ p K v ⥤ ModuleCat.{u} K₀ where
  obj X := ModuleCat.of K₀ X
  map f := ModuleCat.ofHom f.toLinearMap

/-- The forgetful functor to `K₀`-vector spaces is faithful. -/
instance : (forgetToModuleCat.{u} σ p K v).Faithful where
  map_injective h := hom_ext (congrArg ModuleCat.Hom.hom h)

/-- The forgetful functor to `K₀`-vector spaces is additive. -/
instance : (forgetToModuleCat.{u} σ p K v).Additive where
  map_add := rfl

/-! ### The abelian structure -/

section Abelian

variable [hv : Fact (∀ x, v (σ x) = v x)]

/-- The binary biproduct cone of `X` and `Y` in `WeaklyAdmissibleCat σ p K v`, for an additive
valuation `v` with `v ∘ σ = v` (a `Fact`): the direct sum `X × Y` (`FilteredPhiNModule.prod`,
weakly admissible by `FilteredPhiNModule.IsWeaklyAdmissible.prod`) with its projections and
inclusions. -/
def binaryBicone (X Y : WeaklyAdmissibleCat.{u} σ p K v) : BinaryBicone X Y where
  pt := of (X × Y) (X.str.prod Y.str)
    (IsWeaklyAdmissible.prod hv.out X.isWeaklyAdmissible Y.isWeaklyAdmissible)
  fst := FilteredPhiNModule.fst X.str Y.str
  snd := FilteredPhiNModule.snd X.str Y.str
  inl := FilteredPhiNModule.inl X.str Y.str
  inr := FilteredPhiNModule.inr X.str Y.str
  inl_fst := hom_ext (LinearMap.fst_comp_inl K₀ X Y)
  inl_snd := hom_ext (LinearMap.snd_comp_inl K₀ X Y)
  inr_fst := hom_ext (LinearMap.fst_comp_inr K₀ X Y)
  inr_snd := hom_ext (LinearMap.snd_comp_inr K₀ X Y)

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), `WeaklyAdmissibleCat σ p K v` has
binary biproducts, given by the direct sum (`FilteredPhiNModule.prod`). -/
instance : HasBinaryBiproducts (WeaklyAdmissibleCat.{u} σ p K v) :=
  ⟨fun X Y => hasBinaryBiproduct_of_total (binaryBicone X Y) <| hom_ext <|
    show LinearMap.inl K₀ X Y ∘ₗ LinearMap.fst K₀ X Y + LinearMap.inr K₀ X Y ∘ₗ
      LinearMap.snd K₀ X Y = LinearMap.id from LinearMap.ext fun x => by simp⟩

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), `WeaklyAdmissibleCat σ p K v` has
finite products. -/
instance : HasFiniteProducts (WeaklyAdmissibleCat.{u} σ p K v) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), `WeaklyAdmissibleCat σ p K v` has
finite biproducts. -/
instance : HasFiniteBiproducts (WeaklyAdmissibleCat.{u} σ p K v) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable (f : X ⟶ Y)

/-- The kernel object of a morphism `f : X ⟶ Y` in `WeaklyAdmissibleCat σ p K v`, for an additive
valuation `v` with `v ∘ σ = v` (a `Fact`): `Ker f` with the filtration induced from `X`, weakly
admissible by Fontaine–Ouyang, Proposition 8.41 (1) (`FilteredPhiNModule.IsWeaklyAdmissible.ker`).
-/
abbrev kernelObj : WeaklyAdmissibleCat.{u} σ p K v :=
  of (LinearMap.ker f.toLinearMap) (X.str.restrict _ f.isStable_ker)
    (IsWeaklyAdmissible.ker hv.out X.isWeaklyAdmissible Y.isWeaklyAdmissible f)

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the inclusion `Ker f ⟶ X` of the
kernel of `f : X ⟶ Y` with the induced filtration. -/
abbrev kernelι : kernelObj f ⟶ X :=
  X.str.subtype _ f.isStable_ker

/-- The kernel fork of a morphism `f : X ⟶ Y` in `WeaklyAdmissibleCat σ p K v`, for an additive
valuation `v` with `v ∘ σ = v` (a `Fact`): the inclusion into `X` of `Ker f` with the filtration
induced from `X`. -/
def kernelFork : KernelFork f :=
  KernelFork.ofι (kernelι f) (hom_ext (LinearMap.comp_ker_subtype _))

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the inclusion of `Ker f` with the
induced filtration (`WeaklyAdmissibleCat.kernelFork`) is a kernel of `f`. -/
def kernelIsLimit : IsLimit (kernelFork f) :=
  isLimitKernelFork (kernelι f) (hom_ext (LinearMap.comp_ker_subtype _))
    (Submodule.injective_subtype _)
    (Submodule.range_subtype _).ge fun _ => le_rfl

/-- The cokernel object of a morphism `f : X ⟶ Y` in `WeaklyAdmissibleCat σ p K v`, for an
additive valuation `v` with `v ∘ σ = v` (a `Fact`): `Y ⧸ Im f` with the quotient filtration,
weakly admissible by Fontaine–Ouyang, Proposition 8.41 (2)
(`FilteredPhiNModule.IsWeaklyAdmissible.coker`). -/
abbrev cokernelObj : WeaklyAdmissibleCat.{u} σ p K v :=
  of (Y ⧸ LinearMap.range f.toLinearMap) (Y.str.quotient _ f.isStable_range)
    (IsWeaklyAdmissible.coker hv.out X.isWeaklyAdmissible Y.isWeaklyAdmissible f)

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the projection `Y ⟶ Y ⧸ Im f`
onto the cokernel of `f : X ⟶ Y` with the quotient filtration. -/
abbrev cokernelπ : Y ⟶ cokernelObj f :=
  Y.str.mkQ _ f.isStable_range

/-- The cokernel cofork of a morphism `f : X ⟶ Y` in `WeaklyAdmissibleCat σ p K v`, for an
additive valuation `v` with `v ∘ σ = v` (a `Fact`): the projection of `Y` onto `Y ⧸ Im f` with
the quotient filtration. -/
def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (hom_ext (LinearMap.range_mkQ_comp _))

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the projection onto `Y ⧸ Im f`
with the quotient filtration (`WeaklyAdmissibleCat.cokernelCofork`) is a cokernel of `f`. -/
def cokernelIsColimit : IsColimit (cokernelCofork f) :=
  isColimitCokernelCofork (cokernelπ f) (hom_ext (LinearMap.range_mkQ_comp _))
    (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).le
    fun _ => le_rfl

/-- The image of a morphism `f : X ⟶ Y` in `WeaklyAdmissibleCat σ p K v`, for an additive
valuation `v` with `v ∘ σ = v` (a `Fact`): `Im f` with the filtration induced from `Y`, weakly
admissible by `FilteredPhiNModule.IsWeaklyAdmissible.range`. -/
abbrev image : WeaklyAdmissibleCat.{u} σ p K v :=
  of (LinearMap.range f.toLinearMap) (Y.str.restrict _ f.isStable_range)
    (IsWeaklyAdmissible.range hv.out X.isWeaklyAdmissible Y.isWeaklyAdmissible f)

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the corestriction `X ⟶ Im f` of
`f : X ⟶ Y` to its image with the filtration induced from `Y`. -/
abbrev imageπ : X ⟶ image f :=
  Hom.rangeRestrict f

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the inclusion `Im f ⟶ Y` of the
image of `f : X ⟶ Y` with the filtration induced from `Y`. -/
abbrev imageι : image f ⟶ Y :=
  Y.str.subtype _ f.isStable_range

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the inclusion of the kernel of
`f : X ⟶ Y` followed by the corestriction of `f` to its image is zero. -/
theorem kernelι_comp_imageπ : kernelι f ≫ imageπ f = 0 :=
  hom_ext <| LinearMap.ext fun x => Subtype.ext (LinearMap.mem_ker.mp x.2)

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the inclusion of the image of
`f : X ⟶ Y` followed by the projection onto its cokernel is zero. -/
theorem imageι_comp_cokernelπ : imageι f ≫ cokernelπ f = 0 :=
  hom_ext <| LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).mpr x.2

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the factorization of
`f : X ⟶ Y` as a cokernel of its kernel followed by a kernel of its cokernel: the image `Im f`
with the filtration induced from `Y` is the cokernel of `Ker f → X` because, by the strictness
of `f`, that filtration is the quotient filtration from `X`
(`FilteredPhiNModule.IsWeaklyAdmissible.restrict_range_fil_fil`). -/
def abelianStruct : Abelian.AbelianStruct f where
  kernelFork := kernelFork f
  isLimitKernelFork := kernelIsLimit f
  cokernelCofork := cokernelCofork f
  isColimitCokernelCofork := cokernelIsColimit f
  image := image f
  imageπ := imageπ f
  ι_imageπ := kernelι_comp_imageπ f
  imageIsCokernel := isColimitCokernelCofork (imageπ f) (kernelι_comp_imageπ f)
    f.toLinearMap.surjective_rangeRestrict
    (show LinearMap.ker f.toLinearMap.rangeRestrict ≤
      LinearMap.range (LinearMap.ker f.toLinearMap).subtype by
        rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype])
    fun i => (IsWeaklyAdmissible.restrict_range_fil_fil hv.out X.isWeaklyAdmissible
      Y.isWeaklyAdmissible f i).le
  imageι := imageι f
  imageι_π := imageι_comp_cokernelπ f
  imageIsKernel := isLimitKernelFork (imageι f) (imageι_comp_cokernelπ f)
    (Submodule.injective_subtype _)
    (show LinearMap.ker (LinearMap.range f.toLinearMap).mkQ ≤
      LinearMap.range (LinearMap.range f.toLinearMap).subtype by
        rw [Submodule.ker_mkQ, Submodule.range_subtype])
    fun _ => le_rfl
  fac := Hom.subtype_comp_rangeRestrict f

/-- Fontaine–Ouyang, Proposition 8.41, and Fontaine, Exposé III, §4.4.4: for an additive
valuation `v` with `v ∘ σ = v` (a `Fact`), the category `WeaklyAdmissibleCat σ p K v` of
finite-dimensional weakly admissible filtered `(φ, N)`-modules is abelian. -/
instance instAbelian : Abelian (WeaklyAdmissibleCat.{u} σ p K v) :=
  Abelian.mk' fun _ _ f => ⟨abelianStruct f⟩

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the forgetful functor to
`K₀`-vector spaces preserves the kernel of every morphism. -/
instance : PreservesLimit (parallelPair f 0) (forgetToModuleCat.{u} σ p K v) :=
  preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
    ((KernelFork.isLimitMapConeEquiv _ _).symm
      (IsLimit.ofIsoLimit (ModuleCat.kernelIsLimit _)
        (Fork.ext (Iso.refl _) (by ext; rfl))))

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the forgetful functor to
`K₀`-vector spaces preserves the cokernel of every morphism. -/
instance : PreservesColimit (parallelPair f 0) (forgetToModuleCat.{u} σ p K v) :=
  preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
      (IsColimit.ofIsoColimit (ModuleCat.cokernelIsColimit _)
        (Cofork.ext (Iso.refl _) (by ext; rfl))))

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the forgetful functor to
`K₀`-vector spaces is left exact: it preserves finite limits. -/
instance : PreservesFiniteLimits (forgetToModuleCat.{u} σ p K v) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the forgetful functor to
`K₀`-vector spaces is right exact: it preserves finite colimits. -/
instance : PreservesFiniteColimits (forgetToModuleCat.{u} σ p K v) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- For an additive valuation `v` with `v ∘ σ = v` (a `Fact`), the forgetful functor to
`K₀`-vector spaces reflects isomorphisms: a morphism of weakly admissible filtered
`(φ, N)`-modules whose underlying `K₀`-linear map is bijective is an isomorphism. -/
instance : (forgetToModuleCat.{u} σ p K v).ReflectsIsomorphisms where
  reflects f _ := by
    have : Mono f := (forgetToModuleCat.{u} σ p K v).mono_of_mono_map inferInstance
    have : Epi f := (forgetToModuleCat.{u} σ p K v).epi_of_epi_map inferInstance
    exact isIso_of_mono_of_epi f

end Abelian

end WeaklyAdmissibleCat

end FilteredPhiNModule
