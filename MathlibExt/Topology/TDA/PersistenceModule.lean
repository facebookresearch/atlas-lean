/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Persistence modules, interval modules, interleavings and matchings

A persistence module over a preorder `T` is a functor from `T` (viewed as a category) to vector
spaces (G. Carlsson, *Topology and data*, Bull. AMS 46 (2009), Def. 2.9; W. Crawley-Boevey,
*Decomposition of pointwise finite-dimensional persistence modules*, J. Algebra Appl. 14 (2015),
§1). In Lean this is simply a functor `T ⥤ ModuleCat k`; no new structure is introduced.

* `intervalModule k I hI`: the interval module `k_I` of an order-connected set `I ⊆ T`, with
  `k` on `I`, `0` off `I`, and identity maps inside `I` (Crawley-Boevey, §1).
* `Interleaving U V δ`: a `δ`-interleaving between two functors `ℝ ⥤ C` (F. Chazal, V. de Silva,
  M. Glisse, S. Oudot, *The structure and stability of persistence modules*, Springer 2016,
  arXiv:1207.3674, §3.2, diagrams (3.1)); `Interleaving.refl`, `Interleaving.symm`, and
  `Interleaving.trans` (the triangle inequality, Prop. 4.3).
* `IsMatching I J δ`: a `δ`-matching between two families of real intervals, the bottleneck
  matchings of persistence diagrams (Chazal–de Silva–Glisse–Oudot, §4.2) read on the intervals.

The decomposition, uniqueness and stability theorems that use these definitions are recorded in
`WantedExt.Topology.PersistenceModuleWanted`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace MathlibExt.Topology.TDA

section IntervalModule

variable (k : Type u) [Field k] {T : Type*} [Preorder T]

/-- **Structure maps of an interval module.** The map from the fibre at `s` to the fibre at `t`:
the identity of `k` when `s, t ∈ I`, and zero otherwise (Crawley-Boevey, J. Algebra Appl. 14
(2015), §1, `ρ_ts = 1` for `s, t ∈ I`). The fibre at `t` is `PLift (t ∈ I) → k`, which is `k`
when `t ∈ I` and the zero space otherwise. -/
noncomputable def intervalModuleMap (I : Set T) (s t : T) :
    (PLift (s ∈ I) → k) →ₗ[k] (PLift (t ∈ I) → k) where
  toFun f := fun _ => open scoped Classical in if hs : s ∈ I then f ⟨hs⟩ else 0
  map_add' f g := by
    funext _
    by_cases hs : s ∈ I
    · simp [hs]
    · simp [hs]
  map_smul' c f := by
    funext _
    by_cases hs : s ∈ I
    · simp [hs]
    · simp [hs]

/-- **Interval module.** For an order-connected set `I ⊆ T` (an interval when nonempty), the
interval module `k_I : T ⥤ ModuleCat k` has fibre `k` at every `t ∈ I` and `0` elsewhere, with
identity structure maps between points of `I` and zero maps otherwise (Crawley-Boevey,
J. Algebra Appl. 14 (2015), §1; Carlsson, *Topology and data*, Bull. AMS 2009, the modules
`U(m, n)` before Prop. 2.12). Order-connectedness is what makes the structure maps compose. -/
noncomputable def intervalModule (I : Set T) (hI : I.OrdConnected) : T ⥤ ModuleCat.{u} k where
  obj t := ModuleCat.of k (PLift (t ∈ I) → k)
  map {s t} _ := ModuleCat.ofHom (intervalModuleMap k I s t)
  map_id t := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun ht => ?_)
    simp [intervalModuleMap, ht.down]
  map_comp {s t r} hst htr := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun hr => ?_)
    by_cases hs : s ∈ I
    · have ht : t ∈ I := hI.out hs hr.down ⟨leOfHom hst, leOfHom htr⟩
      simp [intervalModuleMap, hs, ht]
    · simp [intervalModuleMap, hs]

theorem intervalModule_obj (I : Set T) (hI : I.OrdConnected) (t : T) :
    (intervalModule k I hI).obj t = ModuleCat.of k (PLift (t ∈ I) → k) :=
  rfl

end IntervalModule

section Interleaving

variable {C : Type*} [Category C]

/-- **`δ`-interleaving.** For `δ ≥ 0` and two functors `U V : ℝ ⥤ C` (persistence modules when
`C` is a category of vector spaces), a `δ`-interleaving consists of maps
`φ t : U t ⟶ V (t + δ)` and `ψ t : V t ⟶ U (t + δ)`, natural in `t`, whose composites
`U t ⟶ V (t + δ) ⟶ U (t + 2δ)` and `V t ⟶ U (t + δ) ⟶ V (t + 2δ)` are the structure maps
(Chazal, de Silva, Glisse and Oudot, *The structure and stability of persistence modules*,
arXiv:1207.3674, §3.2, diagrams (3.1); stated there for `C` the category of vector spaces).
The interleaving distance is the infimum of the `δ` for which one exists. -/
structure Interleaving (U V : ℝ ⥤ C) (δ : ℝ) where
  /-- The scale is nonnegative. -/
  nonneg : 0 ≤ δ
  /-- The shifted map from `U` to `V`. -/
  φ : ∀ t : ℝ, U.obj t ⟶ V.obj (t + δ)
  /-- The shifted map from `V` to `U`. -/
  ψ : ∀ t : ℝ, V.obj t ⟶ U.obj (t + δ)
  /-- `φ` is a homomorphism of degree `δ`. -/
  φ_natural : ∀ (s t : ℝ) (h : s ≤ t),
    U.map (homOfLE h) ≫ φ t = φ s ≫ V.map (homOfLE (by linarith : s + δ ≤ t + δ))
  /-- `ψ` is a homomorphism of degree `δ`. -/
  ψ_natural : ∀ (s t : ℝ) (h : s ≤ t),
    V.map (homOfLE h) ≫ ψ t = ψ s ≫ U.map (homOfLE (by linarith : s + δ ≤ t + δ))
  /-- `ψ ∘ φ` is the structure map of `U` over `2δ`. -/
  ψ_comp_φ : ∀ t : ℝ, φ t ≫ ψ (t + δ) = U.map (homOfLE (by linarith : t ≤ t + δ + δ))
  /-- `φ ∘ ψ` is the structure map of `V` over `2δ`. -/
  φ_comp_ψ : ∀ t : ℝ, ψ t ≫ φ (t + δ) = V.map (homOfLE (by linarith : t ≤ t + δ + δ))

namespace Interleaving

/-- **Interleaving is symmetric.** A `δ`-interleaving between `U` and `V` gives one between `V`
and `U` by exchanging the two families of maps (Chazal–de Silva–Glisse–Oudot, §3.2: the
interleaving distance is symmetric). -/
def symm {U V : ℝ ⥤ C} {δ : ℝ} (e : Interleaving U V δ) : Interleaving V U δ where
  nonneg := e.nonneg
  φ := e.ψ
  ψ := e.φ
  φ_natural := e.ψ_natural
  ψ_natural := e.φ_natural
  ψ_comp_φ := e.φ_comp_ψ
  φ_comp_ψ := e.ψ_comp_φ

/-- **Every functor is `δ`-interleaved with itself for every `δ ≥ 0`**, using its own structure
maps `U t ⟶ U (t + δ)` in both directions (Chazal–de Silva–Glisse–Oudot, §3.2: the shift map
`1_V^δ`). -/
def refl (U : ℝ ⥤ C) {δ : ℝ} (hδ : 0 ≤ δ) : Interleaving U U δ where
  nonneg := hδ
  φ t := U.map (homOfLE (by linarith : t ≤ t + δ))
  ψ t := U.map (homOfLE (by linarith : t ≤ t + δ))
  φ_natural s t h := by simp only [← Functor.map_comp]; rfl
  ψ_natural s t h := by simp only [← Functor.map_comp]; rfl
  ψ_comp_φ t := by simp only [← Functor.map_comp]; rfl
  φ_comp_ψ t := by simp only [← Functor.map_comp]; rfl

/-- In a functor out of `ℝ`, the composite of two structure maps is the structure map. -/
private theorem map_homOfLE_comp {U : ℝ ⥤ C} {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    U.map (homOfLE h₁) ≫ U.map (homOfLE h₂) = U.map (homOfLE (h₁.trans h₂)) := by
  rw [← U.map_comp]
  rfl

private theorem map_homOfLE_comp_assoc {U : ℝ ⥤ C} {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c)
    {Z : C} (x : U.obj c ⟶ Z) :
    U.map (homOfLE h₁) ≫ U.map (homOfLE h₂) ≫ x = U.map (homOfLE (h₁.trans h₂)) ≫ x := by
  rw [← Category.assoc, map_homOfLE_comp]

/-- **Triangle inequality for interleavings.** A `δ₁`-interleaving between `U` and `V` and a
`δ₂`-interleaving between `V` and `W` compose to a `(δ₁ + δ₂)`-interleaving between `U` and `W`,
so the interleaving distance satisfies the triangle inequality (Chazal, de Silva, Glisse and
Oudot, arXiv:1207.3674, Prop. 4.3). -/
def trans {U V W : ℝ ⥤ C} {δ₁ δ₂ : ℝ} (e₁ : Interleaving U V δ₁) (e₂ : Interleaving V W δ₂) :
    Interleaving U W (δ₁ + δ₂) where
  nonneg := add_nonneg e₁.nonneg e₂.nonneg
  φ t := e₁.φ t ≫ e₂.φ (t + δ₁) ≫ W.map (homOfLE (le_of_eq (add_assoc t δ₁ δ₂)))
  ψ t := e₂.ψ t ≫ e₁.ψ (t + δ₂) ≫ U.map (homOfLE (le_of_eq (by ring)))
  φ_natural s t h := by
    rw [← Category.assoc, e₁.φ_natural s t h, Category.assoc,
      reassoc_of% (e₂.φ_natural (s + δ₁) (t + δ₁) (by linarith)),
      map_homOfLE_comp, Category.assoc, Category.assoc, map_homOfLE_comp]
  ψ_natural s t h := by
    rw [← Category.assoc, e₂.ψ_natural s t h, Category.assoc,
      reassoc_of% (e₁.ψ_natural (s + δ₂) (t + δ₂) (by linarith)),
      map_homOfLE_comp, Category.assoc, Category.assoc, map_homOfLE_comp]
  ψ_comp_φ t := by
    simp only [Category.assoc]
    rw [reassoc_of% (e₂.ψ_natural (t + δ₁ + δ₂) (t + (δ₁ + δ₂)) (le_of_eq (add_assoc t δ₁ δ₂))),
      reassoc_of% (e₂.ψ_comp_φ (t + δ₁)), map_homOfLE_comp_assoc,
      reassoc_of% (e₁.ψ_natural (t + δ₁) (t + (δ₁ + δ₂) + δ₂) (by linarith [e₂.nonneg])),
      reassoc_of% (e₁.ψ_comp_φ t), map_homOfLE_comp_assoc, map_homOfLE_comp]
  φ_comp_ψ t := by
    simp only [Category.assoc]
    rw [reassoc_of% (e₁.φ_natural (t + δ₂ + δ₁) (t + (δ₁ + δ₂)) (le_of_eq (by ring))),
      reassoc_of% (e₁.φ_comp_ψ (t + δ₂)), map_homOfLE_comp_assoc,
      reassoc_of% (e₂.φ_natural (t + δ₂) (t + (δ₁ + δ₂) + δ₁) (by linarith [e₁.nonneg])),
      reassoc_of% (e₂.φ_comp_ψ t), map_homOfLE_comp_assoc, map_homOfLE_comp]

end Interleaving

end Interleaving

section Matching

open Metric

/-- **`δ`-matching of barcodes.** Given two families of nonempty real intervals
`I : ι → Set ℝ` and `J : κ → Set ℝ` (the bars of two interval-decomposable persistence modules,
with multiplicity), a `δ`-matching is a partial bijection `M` between the indices such that
matched bars have endpoints within `δ` (measured here by the Hausdorff distance of the
intervals, which for intervals of `ℝ` is the `ℓ^∞` distance between the endpoint pairs, with
infinite endpoints compared as in the source) and every unmatched bar has length at most `2δ`,
i.e. lies within `δ` of the diagonal (Chazal, de Silva, Glisse and Oudot, arXiv:1207.3674, §4.2,
the definition of a partial matching and of a `δ`-matching, for the undecorated diagrams).

The scale is required to be nonnegative, as for interleavings (§3.2, "Let `δ ≥ 0`"): the bottleneck
distance is an infimum over such `δ`, and without the sign condition the truncation
`ENNReal.ofReal δ = 0` would let a negative `δ` match identical bars. The identification of the
Hausdorff distance with the endpoint distance is for nonempty order-connected sets; for closed
bounded intervals it is `hausdorffEDist_Icc_Icc`, and the Hausdorff distance only sees closures
(`Metric.hausdorffEDist_closure`), so it ignores open or closed ends, as the undecorated diagram
does. -/
def IsMatching {ι κ : Type*} (I : ι → Set ℝ) (J : κ → Set ℝ) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ ∃ M : ι → κ → Prop,
    (∀ i j j', M i j → M i j' → j = j') ∧ (∀ i i' j, M i j → M i' j → i = i') ∧
    (∀ i j, M i j → hausdorffEDist (I i) (J j) ≤ ENNReal.ofReal δ) ∧
    (∀ i, (∀ j, ¬ M i j) → ∃ a, I i ⊆ Set.Icc a (a + 2 * δ)) ∧
    (∀ j, (∀ i, ¬ M i j) → ∃ a, J j ⊆ Set.Icc a (a + 2 * δ))

/-- **Matchings are symmetric**: reversing a `δ`-matching between `I` and `J` gives one between
`J` and `I` (so the bottleneck distance is symmetric, Chazal–de Silva–Glisse–Oudot, §4.2). -/
theorem IsMatching.symm {ι κ : Type*} {I : ι → Set ℝ} {J : κ → Set ℝ} {δ : ℝ}
    (h : IsMatching I J δ) : IsMatching J I δ := by
  obtain ⟨hδ, M, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨hδ, fun j i => M i j, fun j i i' hi hi' => h₂ i i' j hi hi',
    fun j j' i hj hj' => h₁ i j j' hj hj', fun j i hji => ?_, h₅, h₄⟩
  rw [hausdorffEDist_comm]
  exact h₃ i j hji

/-- **Hausdorff distance between closed intervals.** For `a ≤ b` and `c ≤ d`, the Hausdorff
distance between `[a, b]` and `[c, d]` is `max |a - c| |b - d|`, the `ℓ^∞` distance between the
points `(a, b)` and `(c, d)` of the persistence plane used for bottleneck matchings (Chazal, de
Silva, Glisse and Oudot, arXiv:1207.3674, §4.2, `d∞`). This is what lets `IsMatching` measure
matched bars by the Hausdorff distance. -/
theorem hausdorffEDist_Icc_Icc {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    hausdorffEDist (Set.Icc a b) (Set.Icc c d) = ENNReal.ofReal (max |a - c| |b - d|) := by
  have key : ∀ {a b c d x : ℝ}, a ≤ x → x ≤ b → c ≤ d →
      |x - max c (min d x)| ≤ max |a - c| |b - d| := by
    intro a b c d x hax hxb hcd
    rcases le_total x d with hxd | hdx
    · rw [min_eq_right hxd]
      rcases le_total c x with hcx | hxc
      · rw [max_eq_right hcx, sub_self, abs_zero]
        exact le_max_of_le_left (abs_nonneg _)
      · rw [max_eq_left hxc]
        calc |x - c| = c - x := by rw [abs_of_nonpos (by linarith)]; ring
          _ ≤ |a - c| := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
          _ ≤ _ := le_max_left _ _
    · rw [min_eq_left hdx, max_eq_right hcd]
      calc |x - d| = x - d := abs_of_nonneg (by linarith)
        _ ≤ |b - d| := by rw [abs_of_nonneg (by linarith)]; linarith
        _ ≤ _ := le_max_right _ _
  apply le_antisymm
  · apply hausdorffEDist_le_of_mem_edist
    · intro x hx
      refine ⟨max c (min d x), ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩, ?_⟩
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (key hx.1 hx.2 hcd)
    · intro y hy
      refine ⟨max a (min b y), ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩, ?_⟩
      rw [edist_dist, Real.dist_eq]
      refine ENNReal.ofReal_le_ofReal ((key hy.1 hy.2 hab).trans_eq ?_)
      rw [abs_sub_comm c a, abs_sub_comm d b]
  · have h₁ : ENNReal.ofReal |a - c| ≤ hausdorffEDist (Set.Icc a b) (Set.Icc c d) := by
      rcases le_total a c with hac | hca
      · refine le_trans ?_ (infEDist_le_hausdorffEDist_of_mem ⟨le_rfl, hab⟩)
        refine le_infEDist.2 fun y hy => ?_
        rw [edist_dist, Real.dist_eq]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [hy.1])]
        linarith [hy.1]
      · rw [hausdorffEDist_comm]
        refine le_trans ?_ (infEDist_le_hausdorffEDist_of_mem ⟨le_rfl, hcd⟩)
        refine le_infEDist.2 fun y hy => ?_
        rw [edist_dist, Real.dist_eq]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith [hy.1])]
        linarith [hy.1]
    have h₂ : ENNReal.ofReal |b - d| ≤ hausdorffEDist (Set.Icc a b) (Set.Icc c d) := by
      rcases le_total d b with hdb | hbd
      · refine le_trans ?_ (infEDist_le_hausdorffEDist_of_mem ⟨hab, le_rfl⟩)
        refine le_infEDist.2 fun y hy => ?_
        rw [edist_dist, Real.dist_eq]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [hy.2])]
        linarith [hy.2]
      · rw [hausdorffEDist_comm]
        refine le_trans ?_ (infEDist_le_hausdorffEDist_of_mem ⟨hcd, le_rfl⟩)
        refine le_infEDist.2 fun y hy => ?_
        rw [edist_dist, Real.dist_eq]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith [hy.2])]
        linarith [hy.2]
    rcases le_total |a - c| |b - d| with h | h
    · rw [max_eq_right h]
      exact h₂
    · rw [max_eq_left h]
      exact h₁

end Matching

end MathlibExt.Topology.TDA
