/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Concavity and homogeneity of the cost function

`V : Set (ι → ℝ)` is the input requirement set for a fixed target output: the input bundles
that can produce at least that output. At input prices `w`, the cost function
`costFn V w = sInf ((fun x => w ⬝ᵥ x) '' V)` is a real `sInf`; it is the economically
meaningful value on `costDomain V`, the prices at which the target is attainable (`V` is
nonempty) and cost is bounded below on `V`. The domain is empty for an unattainable target, so
the real convention `sInf ∅ = 0` is never read as a cost. The cost function is concave on that
(convex) domain and homogeneous of degree one in prices. With an attainable target and
nonnegative bundles, every nonnegative price vector is in the domain. Under attainment the cost
function is the attained minimum.

## Main results

* `MathlibExt.Economics.Producer.concaveOn_costFn`
* `MathlibExt.Economics.Producer.costFn_smul`
* `MathlibExt.Economics.Producer.concaveOn_costFn_nonneg`
* `MathlibExt.Economics.Producer.costFn_eq_of_isLeast`

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Proposition 5.C.2.

Atlas roadmap target EC06.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Producer

/-- The cost function `c(w) = inf_{x ∈ V} w ⬝ᵥ x` for the input requirement set `V`, as a real
`sInf`. It is the economically meaningful value on `costDomain V`. -/
noncomputable def costFn {ι : Type*} [Fintype ι] (V : Set (ι → ℝ)) (w : ι → ℝ) : ℝ :=
  sInf ((fun x => w ⬝ᵥ x) '' V)

/-- The finite-valued domain of the cost function: input prices at which the target output is
attainable (`V` is nonempty) and cost is bounded below on `V`. It is empty when the target is
unattainable, so `sInf ∅ = 0` is never read as a cost. -/
def costDomain {ι : Type*} [Fintype ι] (V : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {w | V.Nonempty ∧ BddBelow ((fun x => w ⬝ᵥ x) '' V)}

/-- The finite-valued domain of the cost function is convex. -/
theorem convex_costDomain {ι : Type*} [Fintype ι] (V : Set (ι → ℝ)) :
    Convex ℝ (costDomain V) := by
  rw [convex_iff_add_mem]
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab
  dsimp [costDomain] at hw₁ hw₂ ⊢
  obtain ⟨hne, m₁, hm₁⟩ := hw₁
  obtain ⟨-, m₂, hm₂⟩ := hw₂
  refine ⟨hne, a * m₁ + b * m₂, ?_⟩
  intro y hy
  obtain ⟨x, hxV, rfl⟩ := hy
  dsimp only
  have h1 : m₁ ≤ w₁ ⬝ᵥ x := hm₁ (Set.mem_image_of_mem _ hxV)
  have h2 : m₂ ≤ w₂ ⬝ᵥ x := hm₂ (Set.mem_image_of_mem _ hxV)
  have e : (a • w₁ + b • w₂) ⬝ᵥ x = a * (w₁ ⬝ᵥ x) + b * (w₂ ⬝ᵥ x) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- **The cost function is concave** in input prices on its finite-valued domain. -/
theorem concaveOn_costFn {ι : Type*} [Fintype ι] (V : Set (ι → ℝ)) :
    ConcaveOn ℝ (costDomain V) (costFn V) := by
  constructor
  · exact convex_costDomain V
  · intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    dsimp [costDomain] at hw₁ hw₂
    obtain ⟨hne, hb₁⟩ := hw₁
    obtain ⟨-, hb₂⟩ := hw₂
    simp only [costFn, smul_eq_mul]
    have hSne : ((fun x => (a • w₁ + b • w₂) ⬝ᵥ x) '' V).Nonempty :=
      hne.image _
    apply le_csInf hSne
    intro y hy
    obtain ⟨x, hxV, rfl⟩ := hy
    dsimp only
    have h1 : sInf ((fun x => w₁ ⬝ᵥ x) '' V) ≤ w₁ ⬝ᵥ x :=
      csInf_le hb₁ (Set.mem_image_of_mem _ hxV)
    have h2 : sInf ((fun x => w₂ ⬝ᵥ x) '' V) ≤ w₂ ⬝ᵥ x :=
      csInf_le hb₂ (Set.mem_image_of_mem _ hxV)
    have e : (a • w₁ + b • w₂) ⬝ᵥ x = a * (w₁ ⬝ᵥ x) + b * (w₂ ⬝ᵥ x) := by
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- **The cost function is homogeneous of degree one** in input prices. -/
theorem costFn_smul {ι : Type*} [Fintype ι] (V : Set (ι → ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (w : ι → ℝ) : costFn V (t • w) = t * costFn V w := by
  unfold costFn
  have hfun : (fun x : ι → ℝ => (t • w) ⬝ᵥ x)
      = (fun c : ℝ => t • c) ∘ (fun x => w ⬝ᵥ x) := by
    funext x
    simp [smul_dotProduct]
  rw [hfun, Set.image_comp, Set.image_smul, Real.sInf_smul_of_nonneg ht, smul_eq_mul]

/-- With an attainable target and nonnegative input bundles, every nonnegative price vector is
in the finite-valued domain. -/
theorem nonneg_subset_costDomain {ι : Type*} [Fintype ι] {V : Set (ι → ℝ)}
    (hne : V.Nonempty) (hV : ∀ x ∈ V, 0 ≤ x) : {w : ι → ℝ | 0 ≤ w} ⊆ costDomain V := by
  intro w hw
  dsimp at hw
  dsimp [costDomain]
  refine ⟨hne, 0, ?_⟩
  intro y hy
  obtain ⟨x, hxV, rfl⟩ := hy
  dsimp only
  exact dotProduct_nonneg_of_nonneg hw (hV x hxV)

/-- With an attainable target and nonnegative input bundles, the cost function is concave on
nonnegative prices. -/
theorem concaveOn_costFn_nonneg {ι : Type*} [Fintype ι] {V : Set (ι → ℝ)}
    (hne : V.Nonempty) (hV : ∀ x ∈ V, 0 ≤ x) : ConcaveOn ℝ {w : ι → ℝ | 0 ≤ w} (costFn V) := by
  exact (concaveOn_costFn V).subset (nonneg_subset_costDomain hne hV) (convex_Ici 0)

/-- Under attainment, the cost function is the attained minimum cost. -/
theorem costFn_eq_of_isLeast {ι : Type*} [Fintype ι] {V : Set (ι → ℝ)} {w : ι → ℝ} {c : ℝ}
    (h : IsLeast ((fun x => w ⬝ᵥ x) '' V) c) : costFn V w = c := by
  unfold costFn
  exact h.csInf_eq

end MathlibExt.Economics.Producer
