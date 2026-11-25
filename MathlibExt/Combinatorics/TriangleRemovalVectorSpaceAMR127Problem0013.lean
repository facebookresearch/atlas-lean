/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Polynomial bounds for triangle removal in 𝔽₂ⁿ (O'Donnell, Problem 14)

R. O'Donnell, Open Problems in Analysis of Boolean Functions, Problem 14 (Triangle Removal in
`𝔽₂ⁿ`): let `A ⊆ 𝔽₂ⁿ`. Suppose that `ε 2ⁿ` elements must be removed from `A` to make it
triangle-free (no `x, y, x + y ∈ A`). Is it true that `Pr_{x,y}[x, y, x + y ∈ A] ≥ poly(ε)` for
independent uniform `x`, `y`?

The answer is yes, by Fox and Lovász: the main result `polynomialTriangleRemoval_holds` proves
`polynomialTriangleRemoval`. The proof follows their argument (J. Fox and L. M. Lovász, A tight
bound for Green's arithmetic triangle removal lemma in vector spaces, arXiv:1606.01230v6) for
`p = 2`, with the weaker exponent `C = γ / (γ - 1) ≈ 25.6`, where `γ = log₂ (72/35)`, in place of
their tight `1 + 1/(5/3 - log₂ 3) ≈ 13.239`:

* a maximal family of pairwise disjoint triangles of `A` has at least `(ε 2ⁿ - 1)/3` members,
  since deleting their vertices and `0` leaves a triangle-free set;
* multicolored sum-free sets: if `x i + y j + z l = 0` holds exactly when `i = j = l` for
  families in `𝔽₂ᵏ`, there are at most `3 (35/18)ᵏ` indices. This is the slice-rank bound for
  tri-colored sum-free sets (J. Blasiak, T. Church, H. Cohn, J. A. Grochow, E. Naslund,
  W. F. Sawin, C. Umans, On cap sets and the group-theoretic approach to matrix multiplication,
  Discrete Analysis 2017:3, arXiv:1605.06702), applied to the tensor
  `∏ₜ (1 + x i t + y j t + z l t)`;
* random kernels (Fox and Lovász, Lemma 5): if every element of pairwise disjoint sets
  `X, Y, Z ⊆ 𝔽₂ⁿ ∖ {0}` lies in at most `Δ` triangles and `6 Δ ≤ 2ʳ ≤ 2ⁿ`, there are at most
  `12 · 4ʳ · (35/18)ⁿ⁻ʳ` triangles: inside the kernel of a uniformly random `r × n` matrix, the
  triangles that are the only ones through each of their vertices form a multicolored sum-free
  family;
* pruning (Fox and Lovász, Lemma 6): starting from the vertex sets of the disjoint triangles,
  repeatedly delete an element lying in at least `2ⁿ (T / 4ⁿ)^(1/γ) / 144` of the `T` remaining
  triangles. Each deletion lowers the potential `(T / 4ⁿ)^(1 - 1/γ)` by a fixed amount, so unless
  `A` has many triangles, fewer than half of the disjoint triangles are destroyed, and the final
  configuration contradicts the random-kernel bound.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.TriangleRemovalVectorSpaceAMR127Problem0013Wanted

/-!
Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 14 (Triangle Removal in 𝔽₂ⁿ). UnsolvedMath record UM-00800444 (`AMR-127-0013`), dataset
ulamai/UnsolvedMath v1.8.0.

"`ε 2ⁿ` elements must be removed" is read as: every triangle-free `B ⊆ A` misses at least `ε 2ⁿ`
elements of `A`. Triangles are ordered and may be degenerate (`x = y` gives `x + y = 0`), as in the
source and in Fox–Lovász (a triangle is an ordered triple with `x + y + z = 0`; in characteristic
`2` the triples in `A³` correspond to the pairs `(x, y)` with `x + y ∈ A`). The probability is
`triangleCount A / 4ⁿ`, and `poly(ε)` means `c ε^C` with constants `c, C > 0` independent of `n` and
`A`; `ε` ranges over `(0, 1]`.
-/

/-- **Triangle-free subsets of $\mathbb{F}_2^n$.** A set $A \subseteq \mathbb{F}_2^n$ is
triangle-free if there are no $x, y \in A$ with $x + y \in A$ (the case $x = y$ is allowed). -/
def IsTriangleFree {n : ℕ} (A : Finset (Fin n → ZMod 2)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x + y ∉ A

/-- **Number of triangles in a subset of $\mathbb{F}_2^n$.** For $A \subseteq \mathbb{F}_2^n$,
the triangle count of $A$ is the number of ordered pairs $(x, y) \in A \times A$ with
$x + y \in A$. Divided by $4^n$, it is the probability that $x, y, x + y \in A$ for independent
uniform $x, y \in \mathbb{F}_2^n$. -/
def triangleCount {n : ℕ} (A : Finset (Fin n → ZMod 2)) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 + p.2 ∈ A).card

/-- **Polynomial triangle removal in $\mathbb{F}_2^n$.** This is the statement that there are
real constants $c > 0$ and $C > 0$ such that for every $n$, every $A \subseteq \mathbb{F}_2^n$
and every real $\varepsilon$ with $0 < \varepsilon \le 1$: if every triangle-free $B \subseteq A$
misses at least $\varepsilon 2^n$ elements of $A$, then the triangle count of $A$ is at least
$c \varepsilon^C 4^n$, that is, $\Pr_{x,y}[x, y, x + y \in A] \ge c \varepsilon^C$ for
independent uniform $x, y \in \mathbb{F}_2^n$.

This is Green's question as posed by O'Donnell (Problem 14); the answer is yes. -/
def polynomialTriangleRemoval : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (ε : ℝ), 0 < ε → ε ≤ 1 →
    (∀ B ⊆ A, IsTriangleFree B → ε * 2 ^ n ≤ ((A \ B).card : ℝ)) →
      c * ε ^ C * 4 ^ n ≤ (triangleCount A : ℝ)

open Finset

/-! ### Multicolored sum-free sets: the slice-rank bound -/

/-- Every subspace `W'` of `ι → F` contains a vector whose support has size at least
`finrank W'`. -/
private theorem exists_mem_finrank_le_card_support {F : Type*} [Field F] [DecidableEq F] {ι : Type*}
    [Fintype ι]
    (W' : Submodule F (ι → F)) :
    ∃ w ∈ W', Module.finrank F W' ≤ #(univ.filter fun i => w i ≠ 0) := by
  classical
  obtain ⟨I, hI, hmin⟩ := (univ.filter fun I : Finset ι =>
    ∀ v ∈ W', (∀ i ∈ I, v i = 0) → v = 0).exists_min_image Finset.card
    ⟨univ, by
      simp only [mem_filter, mem_univ, true_and, forall_const]
      intro v _ hv
      funext i
      exact hv i⟩
  simp only [mem_filter, mem_univ, true_and] at hI hmin
  have h1 : Module.finrank F W' ≤ #I := by
    let f : W' →ₗ[F] (I → F) := (LinearMap.funLeft F F (Subtype.val : I → ι)).comp W'.subtype
    have hf : Function.Injective f := by
      intro v₁ v₂ hv
      have h0 : ((v₁ : ι → F) - v₂) = 0 := by
        apply hI _ (W'.sub_mem v₁.2 v₂.2)
        intro i hi
        have := congr_fun hv ⟨i, hi⟩
        simp only [f, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
          LinearMap.funLeft_apply] at this
        simp [this]
      exact Subtype.ext (sub_eq_zero.1 h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  have h2 : ∀ i ∈ I, ∃ v ∈ W', (∀ j ∈ I, j ≠ i → v j = 0) ∧ v i ≠ 0 := by
    intro i hi
    by_contra hcon
    push Not at hcon
    have hP : ∀ v ∈ W', (∀ j ∈ I.erase i, v j = 0) → v = 0 := by
      intro v hv hvI
      apply hI v hv
      intro j hj
      by_cases hji : j = i
      · subst hji
        exact hcon v hv fun l hl hli => hvI l (mem_erase.2 ⟨hli, hl⟩)
      · exact hvI j (mem_erase.2 ⟨hji, hj⟩)
    have := hmin (I.erase i) hP
    rw [card_erase_of_mem hi] at this
    have : 0 < #I := card_pos.2 ⟨i, hi⟩
    omega
  choose! v hvW hv0 hvi using h2
  refine ⟨∑ i ∈ I, (v i i)⁻¹ • v i, W'.sum_mem fun i hi => W'.smul_mem _ (hvW i hi), ?_⟩
  refine h1.trans (card_le_card fun j hj => ?_)
  simp only [mem_filter, mem_univ, true_and]
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [hvi j hj]
  · intro b hb hbj
    simp [hv0 b hb j hj (Ne.symm hbj)]
  · intro hj'
    exact absurd hj hj'

/-- Tao's slice-rank bound: a diagonal tensor written as a sum of three families of slices
has at most as many points as slices. -/
private theorem card_le_of_diagonal_eq_slices {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    {κ : Type*} (R₁ R₂ R₃ : Finset κ) (f₁ f₂ f₃ : κ → ι → F) (g₁ g₂ g₃ : κ → ι → ι → F)
    (h : ∀ i j l, (if i = j ∧ j = l then (1 : F) else 0) =
      ∑ s ∈ R₁, f₁ s i * g₁ s j l + ∑ s ∈ R₂, f₂ s j * g₂ s i l +
        ∑ s ∈ R₃, f₃ s l * g₃ s i j) :
    Fintype.card ι ≤ #R₁ + #R₂ + #R₃ := by
  classical
  let L : (ι → F) →ₗ[F] (R₁ → F) := Matrix.mulVecLin (Matrix.of fun (s : R₁) i => f₁ s i)
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  have hrange : Module.finrank F (LinearMap.range L) ≤ #R₁ := by
    calc Module.finrank F (LinearMap.range L) ≤ Module.finrank F (R₁ → F) :=
          Submodule.finrank_le _
      _ = #R₁ := by simp
  obtain ⟨w, hw, hwcard⟩ := exists_mem_finrank_le_card_support (LinearMap.ker L)
  have hw' : ∀ s ∈ R₁, ∑ i, w i * f₁ s i = 0 := by
    intro s hs
    have := congr_fun (LinearMap.mem_ker.1 hw) ⟨s, hs⟩
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let U : Matrix ι (R₂ ⊕ R₃) F :=
    Matrix.of fun j => Sum.elim (fun s => f₂ s j) (fun s => ∑ i, w i * g₃ s i j)
  let V : Matrix (R₂ ⊕ R₃) ι F :=
    Matrix.of (Sum.elim (fun s l => ∑ i, w i * g₂ s i l) (fun s l => f₃ s l))
  have hUV : Matrix.diagonal w = U * V := by
    ext j l
    have e1 : Matrix.diagonal w j l =
        ∑ i, w i * (if i = j ∧ j = l then (1 : F) else 0) := by
      rw [Matrix.diagonal_apply, Finset.sum_eq_single j]
      · by_cases hjl : j = l <;> simp [hjl]
      · intro b _ hbj
        simp [hbj]
      · simp
    rw [e1, Matrix.mul_apply, Fintype.sum_sum_type]
    simp_rw [h, mul_add, Finset.sum_add_distrib]
    have e2 : ∑ i, w i * ∑ s ∈ R₁, f₁ s i * g₁ s j l = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro s hs
      simp_rw [← mul_assoc, ← Finset.sum_mul, hw' s hs, zero_mul]
    have e3 : ∑ i, w i * ∑ s ∈ R₂, f₂ s j * g₂ s i l =
        ∑ s : R₂, U j (Sum.inl s) * V (Sum.inl s) l := by
      simp only [U, V, Matrix.of_apply, Sum.elim_inl]
      rw [Finset.sum_coe_sort R₂ (fun s => f₂ s j * ∑ i, w i * g₂ s i l)]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      ring
    have e4 : ∑ i, w i * ∑ s ∈ R₃, f₃ s l * g₃ s i j =
        ∑ s : R₃, U j (Sum.inr s) * V (Sum.inr s) l := by
      simp only [U, V, Matrix.of_apply, Sum.elim_inr]
      rw [Finset.sum_coe_sort R₃ (fun s => (∑ i, w i * g₃ s i j) * f₃ s l)]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [e2, e3, e4, zero_add]
  have hrk : (Matrix.diagonal w).rank ≤ #R₂ + #R₃ := by
    rw [hUV]
    calc (U * V).rank ≤ U.rank := Matrix.rank_mul_le_left U V
      _ ≤ Fintype.card (R₂ ⊕ R₃) := Matrix.rank_le_card_width U
      _ = #R₂ + #R₃ := by simp
  rw [Matrix.rank_diagonal, Fintype.card_subtype] at hrk
  have hcard : Fintype.card ι = Module.finrank F (ι → F) := by simp
  omega

/-- Over `ZMod 2`, `∏ t, (1 + a t)` is the indicator of `a = 0`. -/
private theorem prod_one_add_eq_ite {k : ℕ} (a : Fin k → ZMod 2) (P : Prop) [Decidable P]
    (hP : a = 0 ↔ P) :
    ∏ t, (1 + a t) = if P then 1 else 0 := by
  by_cases hp : P
  · have ha : a = 0 := hP.2 hp
    simp [ha, hp]
  · obtain ⟨t, ht⟩ : ∃ t, a t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hp (hP.1 (funext hcon))
    have key : ∀ r : ZMod 2, r ≠ 0 → 1 + r = 0 := by decide
    rw [ite_eq_right hp]
    exact Finset.prod_eq_zero (mem_univ t) (key _ ht)

/-- Level set of `σ : Fin k → Fin 4` at the value `u`. -/
private def levelSet {k : ℕ} (σ : Fin k → Fin 4) (u : Fin 4) : Finset (Fin k) :=
  univ.filter fun t => σ t = u

/-- Expansion of `∏ t, (1 + (a t + b t + c t))` as a sum over colourings `σ`. -/
private theorem prod_one_add_eq_sum_levelSet {R : Type*} [CommRing R] {k : ℕ} (a b c : Fin k → R) :
    ∏ t, (1 + (a t + b t + c t)) =
      ∑ σ : Fin k → Fin 4, (∏ t ∈ levelSet σ 1, a t) * (∏ t ∈ levelSet σ 2, b t) *
        ∏ t ∈ levelSet σ 3, c t := by
  have h1 : ∀ t, 1 + (a t + b t + c t) = ∑ u : Fin 4,
      (if u = 1 then a t else 1) * (if u = 2 then b t else 1) *
        (if u = 3 then c t else 1) := by
    intro t
    simp [Fin.sum_univ_four, add_assoc]
  simp_rw [h1]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [levelSet, Finset.prod_filter, Finset.prod_mul_distrib]

/-- The levels `1, 2, 3` of `σ` have total size at most `k`. -/
private theorem card_levelSet_add_le {k : ℕ} (σ : Fin k → Fin 4) :
    #(levelSet σ 1) + #(levelSet σ 2) + #(levelSet σ 3) ≤ k := by
  have := Finset.card_eq_sum_card_fiberwise (f := σ) (s := (univ : Finset (Fin k)))
    (t := (univ : Finset (Fin 4))) (fun _ _ => mem_coe.2 (mem_univ _))
  rw [Fin.sum_univ_four, card_univ, Fintype.card_fin] at this
  simp only [levelSet]
  omega

/-- The slice to which a colouring `σ` is assigned: one of the levels `1, 2, 3` of size at
most `k / 3`. -/
private def sliceIndex {k : ℕ} (σ : Fin k → Fin 4) : Fin 4 :=
  if 3 * #(levelSet σ 1) ≤ k then 1 else if 3 * #(levelSet σ 2) ≤ k then 2 else 3

/-- `sliceIndex σ` is one of `1, 2, 3`, and the corresponding level of `σ` is small. -/
private theorem sliceIndex_spec {k : ℕ} (σ : Fin k → Fin 4) :
    sliceIndex σ ≠ 0 ∧ 3 * #(levelSet σ (sliceIndex σ)) ≤ k := by
  have := card_levelSet_add_le σ
  unfold sliceIndex
  split_ifs with h1 h2
  · exact ⟨by decide, h1⟩
  · exact ⟨by decide, h2⟩
  · exact ⟨by decide, by omega⟩

/-- Grouping a sum over colourings according to one of their (small) levels. -/
private theorem sum_levelSet_fiberwise {R : Type*} [CommRing R] {k : ℕ} (s : Finset (Fin k → Fin 4))
    (u : Fin 4)
    (hs : ∀ σ ∈ s, 3 * #(levelSet σ u) ≤ k) (a : Fin k → R) (Q : (Fin k → Fin 4) → R) :
    ∑ σ ∈ s, (∏ t ∈ levelSet σ u, a t) * Q σ =
      ∑ S ∈ univ.filter (fun S : Finset (Fin k) => 3 * #S ≤ k),
        (∏ t ∈ S, a t) * ∑ σ ∈ s.filter (levelSet · u = S), Q σ := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ => levelSet σ u)
    (t := univ.filter (fun S : Finset (Fin k) => 3 * #S ≤ k))
    (fun σ hσ => mem_filter.2 ⟨mem_univ _, hs σ hσ⟩)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [(Finset.mem_filter.1 hσ).2]

/-- Slice decomposition of `∏ t, (1 + (a t + b t + c t))`. -/
private theorem prod_one_add_eq_slices {R : Type*} [CommRing R] {k : ℕ} (a b c : Fin k → R) :
    ∏ t, (1 + (a t + b t + c t)) =
      ∑ S ∈ univ.filter (fun S : Finset (Fin k) => 3 * #S ≤ k), (∏ t ∈ S, a t) *
          ∑ σ ∈ (univ.filter (sliceIndex · = 1)).filter (levelSet · 1 = S),
            (∏ t ∈ levelSet σ 2, b t) * ∏ t ∈ levelSet σ 3, c t +
        ∑ S ∈ univ.filter (fun S : Finset (Fin k) => 3 * #S ≤ k), (∏ t ∈ S, b t) *
          ∑ σ ∈ (univ.filter (sliceIndex · = 2)).filter (levelSet · 2 = S),
            (∏ t ∈ levelSet σ 1, a t) * ∏ t ∈ levelSet σ 3, c t +
        ∑ S ∈ univ.filter (fun S : Finset (Fin k) => 3 * #S ≤ k), (∏ t ∈ S, c t) *
          ∑ σ ∈ (univ.filter (sliceIndex · = 3)).filter (levelSet · 3 = S),
            (∏ t ∈ levelSet σ 1, a t) * ∏ t ∈ levelSet σ 2, b t := by
  have hfib : ∀ u : Fin 4, ∀ σ ∈ (univ : Finset (Fin k → Fin 4)).filter (sliceIndex · = u),
      3 * #(levelSet σ u) ≤ k := by
    intro u σ hσ
    have hu : sliceIndex σ = u := (mem_filter.1 hσ).2
    exact hu ▸ (sliceIndex_spec σ).2
  have h0 : ∀ σ ∈ (univ : Finset (Fin k → Fin 4)).filter (sliceIndex · = 0), False :=
    fun σ hσ => (sliceIndex_spec σ).1 (mem_filter.1 hσ).2
  rw [prod_one_add_eq_sum_levelSet, ← Finset.sum_fiberwise univ sliceIndex, Fin.sum_univ_four,
    Finset.sum_eq_zero (fun σ hσ => (h0 σ hσ).elim), zero_add]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · rw [← sum_levelSet_fiberwise _ 1 (hfib 1)]
    exact Finset.sum_congr rfl fun σ _ => mul_assoc _ _ _
  · rw [← sum_levelSet_fiberwise _ 2 (hfib 2)]
    exact Finset.sum_congr rfl fun σ _ => by ring
  · rw [← sum_levelSet_fiberwise _ 3 (hfib 3)]
    exact Finset.sum_congr rfl fun σ _ => by ring

/-- The number of subsets of `Fin k` of size at most `k / 3` is at most `(35 / 18) ^ k`. -/
private theorem card_small_finsets_le (k : ℕ) :
    ((univ.filter fun S : Finset (Fin k) => 3 * #S ≤ k).card : ℝ) ≤ (35 / 18 : ℝ) ^ k := by
  have hterm : ∀ S : Finset (Fin k), 3 * #S ≤ k → (1 : ℝ) ≤ (3 / 2) ^ k * (8 / 27) ^ #S := by
    intro S hS
    have h1 : (27 / 8 : ℝ) ^ #S ≤ (3 / 2) ^ k := by
      calc (27 / 8 : ℝ) ^ #S = (3 / 2) ^ (3 * #S) := by rw [pow_mul]; norm_num
        _ ≤ (3 / 2) ^ k := pow_le_pow_right₀ (by norm_num) hS
    calc (1 : ℝ) = (27 / 8) ^ #S * (8 / 27) ^ #S := by rw [← mul_pow]; norm_num
      _ ≤ (3 / 2) ^ k * (8 / 27) ^ #S := by gcongr
  calc ((univ.filter fun S : Finset (Fin k) => 3 * #S ≤ k).card : ℝ)
      = ∑ S ∈ univ.filter (fun S : Finset (Fin k) => 3 * #S ≤ k), (1 : ℝ) := by simp
    _ ≤ ∑ S ∈ univ.filter (fun S : Finset (Fin k) => 3 * #S ≤ k),
          (3 / 2 : ℝ) ^ k * (8 / 27) ^ #S :=
        Finset.sum_le_sum fun S hS => hterm S (Finset.mem_filter.1 hS).2
    _ ≤ ∑ S : Finset (Fin k), (3 / 2 : ℝ) ^ k * (8 / 27) ^ #S :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ => by positivity
    _ = (3 / 2 : ℝ) ^ k * (8 / 27 + 1) ^ k := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow (8 / 27 : ℝ) 1 (univ : Finset (Fin k))
        simpa only [one_pow, mul_one, Finset.powerset_univ, Finset.card_univ,
          Fintype.card_fin] using this
    _ = (35 / 18 : ℝ) ^ k := by rw [← mul_pow]; norm_num

/-- Coordinate version of the multicolored sum-free bound. -/
private theorem card_le_of_multicolored {k : ℕ} {ι : Type*} [Fintype ι] (x y z : ι → Fin k → ZMod 2)
    (h : ∀ i j l, x i + y j + z l = 0 ↔ i = j ∧ j = l) :
    Fintype.card ι ≤ 3 * #(univ.filter fun S : Finset (Fin k) => 3 * #S ≤ k) := by
  classical
  have := card_le_of_diagonal_eq_slices (F := ZMod 2)
    (univ.filter fun S : Finset (Fin k) => 3 * #S ≤ k)
    (univ.filter fun S : Finset (Fin k) => 3 * #S ≤ k)
    (univ.filter fun S : Finset (Fin k) => 3 * #S ≤ k)
    (fun S i => ∏ t ∈ S, x i t) (fun S j => ∏ t ∈ S, y j t) (fun S l => ∏ t ∈ S, z l t)
    (fun S j l => ∑ σ ∈ (univ.filter (sliceIndex · = 1)).filter (levelSet · 1 = S),
      (∏ t ∈ levelSet σ 2, y j t) * ∏ t ∈ levelSet σ 3, z l t)
    (fun S i l => ∑ σ ∈ (univ.filter (sliceIndex · = 2)).filter (levelSet · 2 = S),
      (∏ t ∈ levelSet σ 1, x i t) * ∏ t ∈ levelSet σ 3, z l t)
    (fun S i j => ∑ σ ∈ (univ.filter (sliceIndex · = 3)).filter (levelSet · 3 = S),
      (∏ t ∈ levelSet σ 1, x i t) * ∏ t ∈ levelSet σ 2, y j t)
    (fun i j l => by
      rw [← prod_one_add_eq_ite (x i + y j + z l) _ (h i j l)]
      exact prod_one_add_eq_slices (x i) (y j) (z l))
  omega

/-- Multicolored sum-free bound: if `x p + y q + z u = 0` holds exactly when `p = q = u`, for
families indexed by `G` in a subspace `W` of `𝔽₂ⁿ`, then `#G ≤ 3 (35/18) ^ dim W`. -/
private theorem card_le_of_multicolored_of_mem {n : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    {α : Type*}
    (G : Finset α) (x y z : α → Fin n → ZMod 2)
    (hx : ∀ p ∈ G, x p ∈ W) (hy : ∀ p ∈ G, y p ∈ W) (hz : ∀ p ∈ G, z p ∈ W)
    (h : ∀ p ∈ G, ∀ q ∈ G, ∀ u ∈ G, x p + y q + z u = 0 ↔ p = q ∧ q = u) :
    (G.card : ℝ) ≤ 3 * (35 / 18 : ℝ) ^ Module.finrank (ZMod 2) W := by
  let e := (Module.finBasis (ZMod 2) W).equivFun
  let x' : G → Fin (Module.finrank (ZMod 2) W) → ZMod 2 := fun i => e ⟨x i, hx i i.2⟩
  let y' : G → Fin (Module.finrank (ZMod 2) W) → ZMod 2 := fun i => e ⟨y i, hy i i.2⟩
  let z' : G → Fin (Module.finrank (ZMod 2) W) → ZMod 2 := fun i => e ⟨z i, hz i i.2⟩
  have h' : ∀ i j l : G, x' i + y' j + z' l = 0 ↔ i = j ∧ j = l := by
    intro i j l
    have hxyz : x' i + y' j + z' l =
        e ⟨x i + y j + z l, W.add_mem (W.add_mem (hx i i.2) (hy j j.2)) (hz l l.2)⟩ := by
      simp only [x', y', z', ← map_add]
      rfl
    rw [hxyz, LinearEquiv.map_eq_zero_iff]
    simp only [Subtype.ext_iff, Submodule.coe_zero]
    exact h _ i.2 _ j.2 _ l.2
  have h1 := card_le_of_multicolored x' y' z' h'
  have h2 := card_small_finsets_le (Module.finrank (ZMod 2) W)
  rw [Fintype.card_coe] at h1
  calc (G.card : ℝ)
      ≤ 3 * ((univ.filter fun S : Finset (Fin (Module.finrank (ZMod 2) W)) =>
          3 * #S ≤ Module.finrank (ZMod 2) W).card : ℝ) := by exact_mod_cast h1
    _ ≤ 3 * (35 / 18 : ℝ) ^ Module.finrank (ZMod 2) W := by linarith

/-! ### Random kernels: few triangles when every degree is small -/

/-- Triangles of `(X, Y, Z)`: pairs `(x, y) ∈ X × Y` with `x + y ∈ Z`. -/
private def tri {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2)) :
    Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  (X ×ˢ Y).filter fun p => p.1 + p.2 ∈ Z

/-- Number of triangles of `(X, Y, Z)` having `v` as a vertex. -/
private def deg {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2)) (v : Fin n → ZMod 2) : ℕ :=
  ((tri X Y Z).filter fun q => q.1 = v ∨ q.2 = v ∨ q.1 + q.2 = v).card

/-! #### Kernels of random matrices -/

/-- In characteristic `2`, `a + a = 0`. -/
private lemma charTwo_add_self {n : ℕ} (a : Fin n → ZMod 2) : a + a = 0 := by
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize a i = t
  revert t
  decide

/-- In characteristic `2`, `a + b = 0 ↔ a = b`. -/
private lemma charTwo_add_eq_zero_iff {n : ℕ} (a b : Fin n → ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [charTwo_add_self, add_zero]
      _ = (a + b) + b := by rw [add_assoc]
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact charTwo_add_self a

/-- Common kernel of the rows `ψ s`, as a finset. -/
private def kerFinset {n r : ℕ} (ψ : Fin r → Fin n → ZMod 2) : Finset (Fin n → ZMod 2) :=
  univ.filter fun v => ∀ s, ψ s ⬝ᵥ v = 0

/-- `kerFinset ψ` is the kernel of the matrix with rows `ψ`. -/
private lemma mem_kerFinset {n r : ℕ} (ψ : Fin r → Fin n → ZMod 2) (v : Fin n → ZMod 2) :
    v ∈ kerFinset ψ ↔ v ∈ LinearMap.ker (Matrix.of ψ).mulVecLin := by
  simp [kerFinset, funext_iff, Matrix.mulVec]

/-- The kernel of `ψ` has `2 ^ dim` elements. -/
private lemma card_kerFinset {n r : ℕ} (ψ : Fin r → Fin n → ZMod 2) :
    (kerFinset ψ).card = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.of ψ).mulVecLin) := by
  classical
  have h1 := Module.card_eq_pow_finrank (K := ZMod 2)
    (V := LinearMap.ker (Matrix.of ψ).mulVecLin)
  rw [ZMod.card] at h1
  rw [← h1]
  symm
  exact Fintype.card_of_subtype _ (fun v => mem_kerFinset ψ v)

/-- Rank–nullity: the kernel of `r` linear forms has dimension at least `n - r`. -/
private lemma sub_le_finrank_ker {n r : ℕ} (ψ : Fin r → Fin n → ZMod 2) :
    n - r ≤ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.of ψ).mulVecLin) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.of ψ).mulVecLin
  have h2 : Module.finrank (ZMod 2) (LinearMap.range (Matrix.of ψ).mulVecLin) ≤ r := by
    have := Submodule.finrank_le (LinearMap.range (Matrix.of ψ).mulVecLin)
    simpa using this
  rw [Module.finrank_fin_fun] at h1
  omega

/-- The common kernel of `j` independent linear forms has `2 ^ (n - j)` elements. -/
private lemma card_kerFinset_of_linearIndependent {n j : ℕ} (v : Fin j → Fin n → ZMod 2)
    (hv : LinearIndependent (ZMod 2) v) : (kerFinset v).card = 2 ^ (n - j) := by
  rw [card_kerFinset]
  congr 1
  have hrank : (Matrix.of v).rank = j := by
    have := LinearIndependent.rank_matrix (M := Matrix.of v) hv
    simpa using this
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.of v).mulVecLin
  rw [Module.finrank_fin_fun] at h
  rw [Matrix.rank] at hrank
  omega

/-- The number of `ψ` whose kernel contains `j` given independent vectors. -/
private lemma card_matrices_mul_pow {n j : ℕ} (r : ℕ) (v : Fin j → Fin n → ZMod 2)
    (hv : LinearIndependent (ZMod 2) v) :
    (univ.filter fun ψ : Fin r → Fin n → ZMod 2 => ∀ i, v i ∈ kerFinset ψ).card * 2 ^ (j * r) =
      2 ^ (n * r) := by
  have hjn : j ≤ n := by simpa using hv.fintype_card_le_finrank
  have hS := card_kerFinset_of_linearIndependent v hv
  have hset : (univ.filter fun ψ : Fin r → Fin n → ZMod 2 => ∀ i, v i ∈ kerFinset ψ) =
      Fintype.piFinset fun _ => kerFinset v := by
    ext ψ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, kerFinset]
    constructor
    · intro h s i
      rw [dotProduct_comm]
      exact h i s
    · intro h i s
      rw [dotProduct_comm]
      exact h s i
  rw [hset, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, hS, ← pow_mul,
    ← pow_add, ← add_mul, Nat.sub_add_cancel hjn]

/-- A nonzero vector is linearly independent. -/
private lemma linearIndependent_one {n : ℕ} {x : Fin n → ZMod 2} (hx : x ≠ 0) :
    LinearIndependent (ZMod 2) ![x] := by
  rw [linearIndependent_unique_iff]
  simpa using hx

/-- Every element of `ZMod 2` is `0` or `1`. -/
private lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- Over `ZMod 2`, two distinct nonzero vectors are linearly independent. -/
private lemma linearIndependent_two {n : ℕ} {x y : Fin n → ZMod 2} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y) :
    LinearIndependent (ZMod 2) ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at hst
    exact absurd hst hy
  · simp only [zero_smul, one_smul, add_zero] at hst
    exact absurd hst hx
  · simp only [one_smul] at hst
    exact absurd ((charTwo_add_eq_zero_iff x y).1 hst) hxy

/-- Over `ZMod 2`, adding `w ∉ {0, x, y, x + y}` to an independent pair keeps independence. -/
private lemma linearIndependent_three {n : ℕ} {w x y : Fin n → ZMod 2}
    (hxy : LinearIndependent (ZMod 2) ![x, y])
    (h0 : w ≠ 0) (hx : w ≠ x) (hy : w ≠ y) (hs : w ≠ x + y) :
    LinearIndependent (ZMod 2) (Fin.cons w ![x, y] : Fin 3 → Fin n → ZMod 2) := by
  rw [linearIndependent_finCons]
  refine ⟨hxy, ?_⟩
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair]
  rintro ⟨a, b, hab⟩
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp only [zero_smul, one_smul, zero_add, add_zero] at hab
  · exact h0 hab.symm
  · exact hy hab.symm
  · exact hx hab.symm
  · exact hs hab.symm

/-- The number of `r × n` matrices over `ZMod 2`. -/
private lemma card_matrices (n r : ℕ) : Fintype.card (Fin r → Fin n → ZMod 2) = 2 ^ (n * r) := by
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin,
    ← pow_mul]

/-- Since `35 / 18 ≤ 2`, `β ^ d * 2 ^ m ≤ β ^ m * 2 ^ d` for `m ≤ d`. -/
private lemma pow_mul_two_pow_le (m d : ℕ) (h : m ≤ d) :
    (35 / 18 : ℝ) ^ d * 2 ^ m ≤ (35 / 18 : ℝ) ^ m * 2 ^ d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  have he : (35 / 18 : ℝ) ^ e ≤ 2 ^ e := pow_le_pow_left₀ (by norm_num) (by norm_num) e
  calc (35 / 18 : ℝ) ^ (m + e) * 2 ^ m = (35 / 18 : ℝ) ^ m * 2 ^ m * (35 / 18 : ℝ) ^ e := by
        ring
    _ ≤ (35 / 18 : ℝ) ^ m * 2 ^ m * 2 ^ e := by gcongr
    _ = (35 / 18 : ℝ) ^ m * 2 ^ (m + e) := by ring

/-- Triangles of `T` whose two coordinates lie in the kernel of `ψ`. -/
private def kerTriangles {n r : ℕ} (T : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (ψ : Fin r → Fin n → ZMod 2) : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  T.filter fun q => q.1 ∈ kerFinset ψ ∧ q.2 ∈ kerFinset ψ

/-- Triangles of `kerTriangles T ψ` sharing no vertex with any other triangle of
`kerTriangles T ψ`. -/
private def goodTriangles {n r : ℕ} (T : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (ψ : Fin r → Fin n → ZMod 2) : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  (kerTriangles T ψ).filter fun p => ∀ q ∈ kerTriangles T ψ, q ≠ p →
    ¬(q.1 = p.1 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.1 + p.2)

/-- Unfolded membership in `goodTriangles`. -/
private lemma mem_goodTriangles {n r : ℕ} {T : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))}
    {ψ : Fin r → Fin n → ZMod 2} {p : (Fin n → ZMod 2) × (Fin n → ZMod 2)} :
    p ∈ goodTriangles T ψ ↔ (p ∈ T ∧ p.1 ∈ kerFinset ψ ∧ p.2 ∈ kerFinset ψ) ∧
      ∀ q ∈ T, q.1 ∈ kerFinset ψ → q.2 ∈ kerFinset ψ → q ≠ p →
        ¬(q.1 = p.1 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.1 + p.2) := by
  simp only [goodTriangles, kerTriangles, mem_filter, and_imp]

/-- The good triangles form a multicolored sum-free family in `ker ψ`, so there are at most
`3 (35/18) ^ dim (ker ψ)` of them. -/
private lemma card_goodTriangles_le {n r : ℕ} (X Y Z : Finset (Fin n → ZMod 2))
    (ψ : Fin r → Fin n → ZMod 2) :
    ((goodTriangles (tri X Y Z) ψ).card : ℝ) ≤
      3 * (35 / 18 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.of ψ).mulVecLin) := by
  apply card_le_of_multicolored_of_mem _ _ (fun p => p.1) (fun p => p.2) (fun p => p.1 + p.2)
  · intro p hp
    exact (mem_kerFinset ψ _).1 (mem_goodTriangles.1 hp).1.2.1
  · intro p hp
    exact (mem_kerFinset ψ _).1 (mem_goodTriangles.1 hp).1.2.2
  · intro p hp
    have hp' := (mem_goodTriangles.1 hp).1
    exact add_mem ((mem_kerFinset ψ _).1 hp'.2.1) ((mem_kerFinset ψ _).1 hp'.2.2)
  · intro p hp q hq u hu
    rw [mem_goodTriangles] at hp hq hu
    constructor
    · intro h0
      have hsum : p.1 + q.2 = u.1 + u.2 := (charTwo_add_eq_zero_iff _ _).1 h0
      have hpT := hp.1.1
      have hqT := hq.1.1
      have huT := hu.1.1
      simp only [tri, mem_filter, mem_product] at hpT hqT huT
      have hwT : ((p.1, q.2) : (Fin n → ZMod 2) × (Fin n → ZMod 2)) ∈ tri X Y Z := by
        simp only [tri, mem_filter, mem_product]
        exact ⟨⟨hpT.1.1, hqT.1.2⟩, hsum ▸ huT.2⟩
      have hwp : ((p.1, q.2) : (Fin n → ZMod 2) × (Fin n → ZMod 2)) = p := by
        by_contra hne
        exact hp.2 _ hwT hp.1.2.1 hq.1.2.2 hne (Or.inl rfl)
      have hwq : ((p.1, q.2) : (Fin n → ZMod 2) × (Fin n → ZMod 2)) = q := by
        by_contra hne
        exact hq.2 _ hwT hp.1.2.1 hq.1.2.2 hne (Or.inr (Or.inl rfl))
      have hwu : ((p.1, q.2) : (Fin n → ZMod 2) × (Fin n → ZMod 2)) = u := by
        by_contra hne
        exact hu.2 _ hwT hp.1.2.1 hq.1.2.2 hne (Or.inr (Or.inr hsum))
      exact ⟨hwp.symm.trans hwq, hwq.symm.trans hwu⟩
    · rintro ⟨rfl, rfl⟩
      exact charTwo_add_self _

/-- The bound on good triangles, in terms of the size of the kernel. -/
private lemma card_goodTriangles_mul_le {n r : ℕ} (X Y Z : Finset (Fin n → ZMod 2))
    (ψ : Fin r → Fin n → ZMod 2) :
    ((goodTriangles (tri X Y Z) ψ).card : ℝ) * 2 ^ (n - r) ≤
      3 * (35 / 18 : ℝ) ^ (n - r) * (kerFinset ψ).card := by
  have h1 := card_goodTriangles_le X Y Z ψ
  have h3 := sub_le_finrank_ker ψ
  rw [card_kerFinset ψ]
  push_cast
  calc ((goodTriangles (tri X Y Z) ψ).card : ℝ) * 2 ^ (n - r)
      ≤ 3 * (35 / 18 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.of ψ).mulVecLin) *
          2 ^ (n - r) := by gcongr
    _ = 3 * ((35 / 18 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.of ψ).mulVecLin) *
          2 ^ (n - r)) := by ring
    _ ≤ 3 * ((35 / 18 : ℝ) ^ (n - r) *
          2 ^ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.of ψ).mulVecLin)) :=
        mul_le_mul_of_nonneg_left (pow_mul_two_pow_le _ _ h3) (by norm_num)
    _ = _ := by ring

/-- The bound on good triangles, summed over all `ψ`. -/
private lemma sum_card_goodTriangles_le {n r : ℕ} (X Y Z : Finset (Fin n → ZMod 2)) :
    (∑ ψ : Fin r → Fin n → ZMod 2, ((goodTriangles (tri X Y Z) ψ).card : ℝ)) * 2 ^ (n - r) ≤
      3 * (35 / 18 : ℝ) ^ (n - r) * ∑ ψ : Fin r → Fin n → ZMod 2, ((kerFinset ψ).card : ℝ) := by
  rw [sum_mul, mul_sum]
  exact sum_le_sum fun ψ _ => card_goodTriangles_mul_le X Y Z ψ

/-- The total size of the kernels of all `ψ`. -/
private lemma sum_card_kerFinset_le (n r : ℕ) :
    2 ^ r * ∑ ψ : Fin r → Fin n → ZMod 2, (kerFinset ψ).card ≤
      2 ^ r * 2 ^ (n * r) + 2 ^ n * 2 ^ (n * r) := by
  have hswap : ∑ ψ : Fin r → Fin n → ZMod 2, (kerFinset ψ).card =
      ∑ v : Fin n → ZMod 2,
        (univ.filter fun ψ : Fin r → Fin n → ZMod 2 => v ∈ kerFinset ψ).card := by
    simp only [card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun ψ _ => ?_
    rw [kerFinset, card_filter]
    refine sum_congr rfl fun v _ => ?_
    simp
  rw [hswap, ← add_sum_erase univ _ (mem_univ (0 : Fin n → ZMod 2)), mul_add, mul_sum]
  have hf0 : (univ.filter fun ψ : Fin r → Fin n → ZMod 2 =>
      (0 : Fin n → ZMod 2) ∈ kerFinset ψ).card = 2 ^ (n * r) := by
    rw [filter_true_of_mem (fun ψ _ => by simp [kerFinset]), card_univ, card_matrices]
  have hfv : ∀ v ∈ univ.erase (0 : Fin n → ZMod 2),
      2 ^ r * (univ.filter fun ψ : Fin r → Fin n → ZMod 2 => v ∈ kerFinset ψ).card =
        2 ^ (n * r) := by
    intro v hv
    have hv0 : v ≠ 0 := ne_of_mem_erase hv
    have := card_matrices_mul_pow (j := 1) r ![v] (linearIndependent_one hv0)
    rw [one_mul] at this
    rw [mul_comm, ← this]
    congr 2
    exact filter_congr fun ψ _ => by simp
  rw [hf0, sum_congr rfl hfv, sum_const, smul_eq_mul]
  have hcard : (univ.erase (0 : Fin n → ZMod 2)).card ≤ 2 ^ n := by
    calc (univ.erase (0 : Fin n → ZMod 2)).card ≤ (univ : Finset (Fin n → ZMod 2)).card :=
          card_erase_le
      _ = 2 ^ n := by simp [ZMod.card]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hcard) _

/-- At most `3 Δ` triangles share a vertex with a given triangle `p`. -/
private lemma card_neighbours_le {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2)) (Δ : ℕ)
    (hdeg : ∀ v, deg X Y Z v ≤ Δ) (p : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    ((tri X Y Z).filter fun q =>
      q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.1 + p.2)).card ≤ 3 * Δ := by
  have hsub : ((tri X Y Z).filter fun q =>
      q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.1 + p.2)) ⊆
      ((tri X Y Z).filter fun q => q.1 = p.1 ∨ q.2 = p.1 ∨ q.1 + q.2 = p.1) ∪
      ((tri X Y Z).filter fun q => q.1 = p.2 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.2) ∪
      ((tri X Y Z).filter fun q =>
        q.1 = p.1 + p.2 ∨ q.2 = p.1 + p.2 ∨ q.1 + q.2 = p.1 + p.2) := by
    intro q hq
    simp only [mem_filter, mem_union] at hq ⊢
    rcases hq with ⟨hqT, -, h | h | h⟩
    · exact Or.inl (Or.inl ⟨hqT, Or.inl h⟩)
    · exact Or.inl (Or.inr ⟨hqT, Or.inr (Or.inl h)⟩)
    · exact Or.inr ⟨hqT, Or.inr (Or.inr h)⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := hdeg p.1
  have h2 := hdeg p.2
  have h3 := hdeg (p.1 + p.2)
  have h4 := card_union_le
    ((tri X Y Z).filter fun q => q.1 = p.1 ∨ q.2 = p.1 ∨ q.1 + q.2 = p.1)
    ((tri X Y Z).filter fun q => q.1 = p.2 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.2)
  simp only [deg] at h1 h2 h3
  omega

/-- Arithmetic of the per-triangle lower bound. -/
private lemma count_arith (N a g s m Δ P Q : ℕ) (hP : 0 < P) (ha : a * Q = N) (hle : a ≤ g + s)
    (hs : s * (Q * P) = m * N) (hm : m ≤ 3 * Δ) (hΔ : 6 * Δ ≤ P) : N ≤ 2 * Q * g := by
  have h1 : N * P ≤ g * Q * P + 3 * Δ * N := by
    calc N * P = a * Q * P := by rw [ha]
      _ ≤ (g + s) * Q * P := by gcongr
      _ = g * Q * P + s * (Q * P) := by ring
      _ = g * Q * P + m * N := by rw [hs]
      _ ≤ g * Q * P + 3 * Δ * N := by gcongr
  have h2 : 6 * Δ * N ≤ P * N := Nat.mul_le_mul_right N hΔ
  have h3 : N * P ≤ 2 * Q * g * P := by linarith
  exact Nat.le_of_mul_le_mul_right h3 hP

/-- Unfolding a condition over `Fin 2`. -/
private lemma forall_two_mem_kerFinset {n r : ℕ} (ψ : Fin r → Fin n → ZMod 2)
    (a b : Fin n → ZMod 2) :
    (∀ i, ![a, b] i ∈ kerFinset ψ) ↔ a ∈ kerFinset ψ ∧ b ∈ kerFinset ψ := by
  simp [Fin.forall_fin_two]

/-- Unfolding a condition over `Fin 3`. -/
private lemma forall_three_mem_kerFinset {n r : ℕ} (ψ : Fin r → Fin n → ZMod 2)
    (a b c : Fin n → ZMod 2) :
    (∀ i, (Fin.cons a ![b, c] : Fin 3 → Fin n → ZMod 2) i ∈ kerFinset ψ) ↔
      a ∈ kerFinset ψ ∧ b ∈ kerFinset ψ ∧ c ∈ kerFinset ψ := by
  simp [Fin.forall_fin_succ]

/-- A fixed triangle is good for many `ψ`. -/
private lemma pow_le_card_good {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hX0 : (0 : Fin n → ZMod 2) ∉ X) (hY0 : (0 : Fin n → ZMod 2) ∉ Y)
    (Δ r : ℕ) (hΔ : 6 * Δ ≤ 2 ^ r) (hdeg : ∀ v, deg X Y Z v ≤ Δ)
    (p : (Fin n → ZMod 2) × (Fin n → ZMod 2)) (hp : p ∈ tri X Y Z) :
    2 ^ (n * r) ≤ 2 * 2 ^ (2 * r) *
      (univ.filter fun ψ : Fin r → Fin n → ZMod 2 => p ∈ goodTriangles (tri X Y Z) ψ).card := by
  have hp' := hp
  simp only [tri, mem_filter, mem_product] at hp'
  obtain ⟨⟨hp1X, hp2Y⟩, hp3Z⟩ := hp'
  have hp10 : p.1 ≠ 0 := fun h => hX0 (h ▸ hp1X)
  have hp20 : p.2 ≠ 0 := fun h => hY0 (h ▸ hp2Y)
  have hp12 : p.1 ≠ p.2 := fun h => Finset.disjoint_left.1 hXY hp1X (h ▸ hp2Y)
  have hli2 := linearIndependent_two hp10 hp20 hp12
  -- the triangles sharing a vertex with `p`
  set Nb := (tri X Y Z).filter fun q =>
    q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.1 + p.2) with hNb
  -- a vertex of `q` which is not a vertex of `p`
  set w : (Fin n → ZMod 2) × (Fin n → ZMod 2) → Fin n → ZMod 2 :=
    fun q => if q.1 = p.1 then q.2 else q.1 with hw
  set A := univ.filter fun ψ : Fin r → Fin n → ZMod 2 => ∀ i, ![p.1, p.2] i ∈ kerFinset ψ
    with hA
  set G := univ.filter fun ψ : Fin r → Fin n → ZMod 2 => p ∈ goodTriangles (tri X Y Z) ψ
    with hG
  set B : (Fin n → ZMod 2) × (Fin n → ZMod 2) → Finset (Fin r → Fin n → ZMod 2) := fun q =>
    univ.filter fun ψ => ∀ i, (Fin.cons (w q) ![p.1, p.2] : Fin 3 → Fin n → ZMod 2) i ∈ kerFinset ψ
    with hB
  have hAcard : A.card * 2 ^ (2 * r) = 2 ^ (n * r) := card_matrices_mul_pow r _ hli2
  have hBcard : ∀ q ∈ Nb, (B q).card * 2 ^ (3 * r) = 2 ^ (n * r) := by
    intro q hq
    rw [hNb, mem_filter] at hq
    obtain ⟨hqT, hqp, -⟩ := hq
    simp only [tri, mem_filter, mem_product] at hqT
    obtain ⟨⟨hq1X, hq2Y⟩, hq3Z⟩ := hqT
    refine card_matrices_mul_pow r _ (linearIndependent_three hli2 ?_ ?_ ?_ ?_)
    · simp only [hw]
      split_ifs with h
      · exact fun h0 => hY0 (h0 ▸ hq2Y)
      · exact fun h0 => hX0 (h0 ▸ hq1X)
    · simp only [hw]
      split_ifs with h
      · exact fun h' => Finset.disjoint_left.1 hXY hp1X (h' ▸ hq2Y)
      · exact h
    · simp only [hw]
      split_ifs with h
      · exact fun h' => hqp (Prod.ext h h')
      · exact fun h' => Finset.disjoint_left.1 hXY hq1X (h' ▸ hp2Y)
    · simp only [hw]
      split_ifs with h
      · exact fun h' => Finset.disjoint_left.1 hYZ hq2Y (h' ▸ hp3Z)
      · exact fun h' => Finset.disjoint_left.1 hXZ hq1X (h' ▸ hp3Z)
  have hsub : A ⊆ G ∪ Nb.biUnion B := by
    intro ψ hψ
    rw [hA, mem_filter, forall_two_mem_kerFinset] at hψ
    obtain ⟨-, hK1, hK2⟩ := hψ
    rw [mem_union]
    by_cases hgood : p ∈ goodTriangles (tri X Y Z) ψ
    · left
      rw [hG, mem_filter]
      exact ⟨mem_univ _, hgood⟩
    · right
      rw [mem_goodTriangles] at hgood
      push Not at hgood
      obtain ⟨q, hqT, hq1, hq2, hqp, hshare⟩ := hgood ⟨hp, hK1, hK2⟩
      rw [mem_biUnion]
      refine ⟨q, ?_, ?_⟩
      · rw [hNb, mem_filter]
        exact ⟨hqT, hqp, hshare⟩
      · simp only [hB, mem_filter, mem_univ, true_and]
        rw [forall_three_mem_kerFinset]
        refine ⟨?_, hK1, hK2⟩
        simp only [hw]
        split_ifs
        · exact hq2
        · exact hq1
  have hNbcard : Nb.card ≤ 3 * Δ := card_neighbours_le X Y Z Δ hdeg p
  have hle : A.card ≤ G.card + ∑ q ∈ Nb, (B q).card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have hsumB : (∑ q ∈ Nb, (B q).card) * (2 ^ (2 * r) * 2 ^ r) = Nb.card * 2 ^ (n * r) := by
    rw [← pow_add, show 2 * r + r = 3 * r by ring, sum_mul, sum_congr rfl hBcard, sum_const,
      smul_eq_mul]
  exact count_arith _ _ _ _ _ Δ _ _ (by positivity) hAcard hle hsumB hNbcard hΔ

/-- Double counting of pairs `(p, ψ)` with `p` good for `ψ`. -/
private lemma sum_card_good_comm {n r : ℕ} (T : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))) :
    ∑ p ∈ T, (univ.filter fun ψ : Fin r → Fin n → ZMod 2 => p ∈ goodTriangles T ψ).card =
      ∑ ψ : Fin r → Fin n → ZMod 2, (goodTriangles T ψ).card := by
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun ψ _ => ?_
  rw [← card_filter]
  congr 1
  ext p
  simp only [mem_filter, and_iff_right_iff_imp]
  intro hp
  exact (mem_goodTriangles.1 hp).1.1

/-- The lower bound on good triangles, summed over all triangles. -/
private lemma card_tri_mul_le_sum {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hX0 : (0 : Fin n → ZMod 2) ∉ X) (hY0 : (0 : Fin n → ZMod 2) ∉ Y)
    (Δ r : ℕ) (hΔ : 6 * Δ ≤ 2 ^ r) (hdeg : ∀ v, deg X Y Z v ≤ Δ) :
    (tri X Y Z).card * 2 ^ (n * r) ≤
      2 * 2 ^ (2 * r) * ∑ ψ : Fin r → Fin n → ZMod 2, (goodTriangles (tri X Y Z) ψ).card := by
  rw [← sum_card_good_comm, mul_sum, card_eq_sum_ones (tri X Y Z), sum_mul]
  refine sum_le_sum fun p hp => ?_
  rw [one_mul]
  exact pow_le_card_good X Y Z hXY hXZ hYZ hX0 hY0 Δ r hΔ hdeg p hp

/-- The real arithmetic combining the upper and lower bounds on good pairs `(p, ψ)`. -/
private lemma card_tri_le_of_sums (t g k N a b c e f : ℝ) (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (h1 : g * a ≤ 3 * e * k) (h2 : b * k ≤ b * N + c * N)
    (h3 : t * N ≤ 2 * f * g) (hc : a * b = c) (hbc : b ≤ c) : t ≤ 12 * f * e := by
  have hc0 : 0 < c := hc ▸ mul_pos ha hb
  have he3 : 0 ≤ 3 * e := mul_nonneg (by norm_num) he
  have hg : g ≤ 6 * e * N := by
    have hbN : b * N ≤ c * N := mul_le_mul_of_nonneg_right hbc hN.le
    have h4 : g * c ≤ 6 * e * N * c := by
      calc g * c = g * a * b := by rw [← hc]; ring
        _ ≤ 3 * e * k * b := mul_le_mul_of_nonneg_right h1 hb.le
        _ = 3 * e * (b * k) := by ring
        _ ≤ 3 * e * (b * N + c * N) := mul_le_mul_of_nonneg_left h2 he3
        _ ≤ 3 * e * (c * N + c * N) := mul_le_mul_of_nonneg_left (by linarith) he3
        _ = 6 * e * N * c := by ring
    exact le_of_mul_le_mul_right h4 hc0
  have h5 : t * N ≤ 12 * f * e * N := by
    calc t * N ≤ 2 * f * g := h3
      _ ≤ 2 * f * (6 * e * N) := mul_le_mul_of_nonneg_left hg (mul_nonneg (by norm_num) hf)
      _ = 12 * f * e * N := by ring
  exact le_of_mul_le_mul_right h5 hN

/-- Random kernels (Fox–Lovász, Lemma 5, for `p = 2`): if every element of the pairwise disjoint
sets `X, Y ∌ 0` and `Z` lies in at most `Δ` triangles and `6 Δ ≤ 2 ^ r` with `r ≤ n`, then there
are at most `12 · 4 ^ r · (35/18) ^ (n - r)` triangles. -/
private theorem card_tri_le {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hX0 : (0 : Fin n → ZMod 2) ∉ X) (hY0 : (0 : Fin n → ZMod 2) ∉ Y)
    (Δ r : ℕ) (hr : r ≤ n) (hΔ : 6 * Δ ≤ 2 ^ r) (hdeg : ∀ v, deg X Y Z v ≤ Δ) :
    ((tri X Y Z).card : ℝ) ≤ 12 * 4 ^ r * (35 / 18 : ℝ) ^ (n - r) := by
  have hC := card_tri_mul_le_sum X Y Z hXY hXZ hYZ hX0 hY0 Δ r hΔ hdeg
  have hA := sum_card_goodTriangles_le (r := r) X Y Z
  have hB := sum_card_kerFinset_le n r
  have hC' : ((tri X Y Z).card : ℝ) * 2 ^ (n * r) ≤
      2 * 4 ^ r * ∑ ψ : Fin r → Fin n → ZMod 2, ((goodTriangles (tri X Y Z) ψ).card : ℝ) := by
    have h4 : (4 : ℝ) ^ r = 2 ^ (2 * r) := by
      rw [pow_mul]
      norm_num
    rw [h4]
    exact_mod_cast hC
  have hB' : (2 : ℝ) ^ r * ∑ ψ : Fin r → Fin n → ZMod 2, ((kerFinset ψ).card : ℝ) ≤
      2 ^ r * 2 ^ (n * r) + 2 ^ n * 2 ^ (n * r) := by
    exact_mod_cast hB
  have hpow : (2 : ℝ) ^ (n - r) * 2 ^ r = 2 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  have hrn : (2 : ℝ) ^ r ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hr
  exact card_tri_le_of_sums _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hA hB' hC' hpow hrn

/-! ### Pruning, matchings and the final count -/

section Prune

variable {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2))

/-- Triangles with all vertices in `S`. -/
private def triS (S : Finset (Fin n → ZMod 2)) := tri (X ∩ S) (Y ∩ S) (Z ∩ S)

/-- Degree of `v` among the triangles with all vertices in `S`. -/
private def degS (S : Finset (Fin n → ZMod 2)) (v : Fin n → ZMod 2) : ℕ :=
  deg (X ∩ S) (Y ∩ S) (Z ∩ S) v

/-- Deleting `v` removes exactly the triangles through `v`. -/
private lemma prune_triS_erase (S : Finset (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    triS X Y Z (S.erase v) =
      (triS X Y Z S).filter (fun q => ¬(q.1 = v ∨ q.2 = v ∨ q.1 + q.2 = v)) := by
  ext q
  simp only [triS, tri, mem_filter, mem_product, mem_inter, mem_erase]
  constructor
  · intro h
    refine ⟨⟨⟨⟨h.1.1.1, h.1.1.2.2⟩, h.1.2.1, h.1.2.2.2⟩, h.2.1, h.2.2.2⟩, ?_⟩
    rintro (h' | h' | h')
    · exact h.1.1.2.1 h'
    · exact h.1.2.2.1 h'
    · exact h.2.2.1 h'
  · rintro ⟨⟨⟨⟨h1, h3⟩, h4, h6⟩, h7, h9⟩, h10⟩
    exact ⟨⟨⟨h1, fun h => h10 (Or.inl h), h3⟩, h4, fun h => h10 (Or.inr (Or.inl h)), h6⟩, h7,
      fun h => h10 (Or.inr (Or.inr h)), h9⟩

/-- Deleting `v` removes `degS X Y Z S v` triangles. -/
private lemma prune_card_triS_erase (S : Finset (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    (triS X Y Z (S.erase v)).card + degS X Y Z S v = (triS X Y Z S).card := by
  rw [prune_triS_erase, degS, deg, add_comm]
  exact card_filter_add_card_filter_not _

/-- A vertex of positive degree belongs to `S`. -/
private lemma prune_mem_of_degS_pos (S : Finset (Fin n → ZMod 2)) (v : Fin n → ZMod 2)
    (h : 0 < degS X Y Z S v) : v ∈ S := by
  obtain ⟨q, hq⟩ := card_pos.mp h
  simp only [tri, mem_filter, mem_product, mem_inter] at hq
  rcases hq.2 with h1 | h1 | h1 <;> rw [← h1] <;> tauto

/-- Pruning: repeatedly deleting a vertex whose positive degree is at least `τ T`, where `T` is
the current number of triangles, reaches a set in which every positive degree is below the
threshold; if each deletion lowers the potential `P` by at least `1`, the number of deleted
vertices is at most the total drop of `P`. -/
private theorem exists_pruned (τ P : ℕ → ℝ)
    (hP : ∀ T D : ℕ, 0 < D → D ≤ T → τ T ≤ D → P (T - D) + 1 ≤ P T)
    (S : Finset (Fin n → ZMod 2)) :
    ∃ S' ⊆ S, (∀ v, 0 < degS X Y Z S' v → (degS X Y Z S' v : ℝ) < τ (triS X Y Z S').card) ∧
      ((S \ S').card : ℝ) ≤ P (triS X Y Z S).card - P (triS X Y Z S').card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : ∀ v, 0 < degS X Y Z S v → (degS X Y Z S v : ℝ) < τ (triS X Y Z S).card
    · exact ⟨S, subset_refl _, hS, by simp⟩
    · push Not at hS
      obtain ⟨v, hv0, hvτ⟩ := hS
      have hvS : v ∈ S := prune_mem_of_degS_pos X Y Z S v hv0
      obtain ⟨S', hS'sub, hS'deg, hS'card⟩ := ih (S.erase v) (erase_ssubset hvS)
      refine ⟨S', hS'sub.trans (erase_subset _ _), hS'deg, ?_⟩
      have hvS' : v ∉ S' := fun h => by simpa using hS'sub h
      have h1 : (S \ S').card = (S.erase v \ S').card + 1 := by
        rw [erase_sdiff_comm, card_erase_add_one (mem_sdiff.mpr ⟨hvS, hvS'⟩)]
      have h2 := prune_card_triS_erase X Y Z S v
      have h3 := hP (triS X Y Z S).card (degS X Y Z S v) hv0 (by omega) hvτ
      have h4 : (triS X Y Z S).card - degS X Y Z S v = (triS X Y Z (S.erase v)).card := by
        omega
      rw [h4] at h3
      rw [h1]
      push_cast
      linarith

/-- The vertex set of a triangle. -/
private def verts (p : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : Finset (Fin n → ZMod 2) :=
  {p.1, p.2, p.1 + p.2}

/-- If the triangles of `M` are pairwise vertex-disjoint, each deleted vertex destroys at most one
of them, so `#M` is at most the number of surviving triangles plus the number of deleted
vertices. -/
private lemma card_le_card_triS_add (M : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hM : M ⊆ tri X Y Z)
    (hdisj : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → Disjoint (verts p) (verts q))
    (S' : Finset (Fin n → ZMod 2)) :
    M.card ≤ (triS X Y Z S').card + ((X ∪ Y ∪ Z) \ S').card := by
  classical
  have h1 : M.filter (fun p => verts p ⊆ S') ⊆ triS X Y Z S' := by
    intro p hp
    rw [mem_filter] at hp
    have hpT := hM hp.1
    simp only [verts, insert_subset_iff, singleton_subset_iff] at hp
    simp only [triS, tri, mem_filter, mem_product, mem_inter] at hpT ⊢
    exact ⟨⟨⟨hpT.1.1, hp.2.1⟩, hpT.1.2, hp.2.2.1⟩, hpT.2, hp.2.2.2⟩
  have h2 : (M.filter (fun p => ¬ verts p ⊆ S')).card ≤ ((X ∪ Y ∪ Z) \ S').card := by
    let f : (Fin n → ZMod 2) × (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun p =>
      if p.1 ∉ S' then p.1 else if p.2 ∉ S' then p.2 else p.1 + p.2
    have hfv : ∀ p, f p ∈ verts p := by
      intro p
      simp only [f, verts, mem_insert, mem_singleton]
      split_ifs <;> simp
    have hfS : ∀ p, ¬ verts p ⊆ S' → f p ∉ S' := by
      intro p hp
      simp only [verts, insert_subset_iff, singleton_subset_iff, not_and_or] at hp
      simp only [f]
      split_ifs <;> tauto
    refine card_le_card_of_injOn f ?_ ?_
    · intro p hp
      rw [mem_coe, mem_filter] at hp
      have hpT := hM hp.1
      simp only [tri, mem_filter, mem_product] at hpT
      rw [mem_coe, mem_sdiff]
      refine ⟨?_, hfS p hp.2⟩
      have := hfv p
      simp only [verts, mem_insert, mem_singleton] at this
      simp only [mem_union]
      rcases this with h | h | h <;> rw [h] <;> tauto
    · intro p hp q hq hpq
      rw [mem_coe, mem_filter] at hp hq
      by_contra hne
      exact disjoint_left.mp (hdisj p hp.1 q hq.1 hne) (hfv p) (hpq ▸ hfv q)
  have h3 := card_filter_add_card_filter_not (s := M) (fun p => verts p ⊆ S')
  have h4 := card_le_card h1
  omega

end Prune

/-- Greedy matching: `A` has a family `M` of pairwise vertex-disjoint triangles with three distinct
nonzero vertices, and a triangle-free subset `B` with `#(A \ B) ≤ 3 #M + 1`. -/
private theorem exists_disjoint_triangles {n : ℕ} (A : Finset (Fin n → ZMod 2)) :
    ∃ M : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)), ∃ B ⊆ A, IsTriangleFree B ∧
      (A \ B).card ≤ 3 * M.card + 1 ∧
      (∀ p ∈ M, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 ∈ A) ∧
      (∀ p ∈ M, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2) ∧
      (∀ p ∈ M, ∀ q ∈ M, p ≠ q → Disjoint (verts p) (verts q)) := by
  classical
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases hA : ∃ x ∈ A, ∃ y ∈ A, x + y ∈ A ∧ x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y
    · obtain ⟨x, hx, y, hy, hxy, hx0, hy0, hne⟩ := hA
      set A' := A \ verts (x, y) with hA'
      have hxA' : x ∉ A' := by simp [hA', verts]
      have hA'A : A' ⊂ A := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun h => hxA' (h ▸ hx)⟩
      obtain ⟨M', B', hB'A', hB'free, hcard, hM'A, hM'nd, hM'disj⟩ := ih A' hA'A
      refine ⟨insert (x, y) M', B', hB'A'.trans sdiff_subset, hB'free, ?_, ?_, ?_, ?_⟩
      · have hnot : (x, y) ∉ M' := fun h => hxA' (hM'A _ h).1
        rw [card_insert_of_notMem hnot]
        have : A \ B' ⊆ (A' \ B') ∪ verts (x, y) := by
          intro v hv
          rw [mem_sdiff] at hv
          by_cases hvv : v ∈ verts (x, y)
          · exact mem_union_right _ hvv
          · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hv.1, hvv⟩, hv.2⟩)
        have h1 := card_le_card this
        have h2 := card_union_le (A' \ B') (verts (x, y))
        have h3 : (verts (x, y)).card ≤ 3 := by
          simp only [verts]
          exact card_le_three
        omega
      · intro p hp
        rw [mem_insert] at hp
        rcases hp with rfl | hp
        · exact ⟨hx, hy, hxy⟩
        · have := hM'A p hp
          exact ⟨sdiff_subset this.1, sdiff_subset this.2.1, sdiff_subset this.2.2⟩
      · intro p hp
        rw [mem_insert] at hp
        rcases hp with rfl | hp
        · exact ⟨hx0, hy0, hne⟩
        · exact hM'nd p hp
      · have key : ∀ q ∈ M', Disjoint (verts (x, y)) (verts q) := by
          intro q hq
          have hq' := hM'A q hq
          rw [disjoint_right]
          intro v hv
          simp only [verts, mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl | rfl
          · exact (mem_sdiff.mp hq'.1).2
          · exact (mem_sdiff.mp hq'.2.1).2
          · exact (mem_sdiff.mp hq'.2.2).2
        intro p hp q hq hpq
        rw [mem_insert] at hp hq
        rcases hp with rfl | hp <;> rcases hq with rfl | hq
        · exact absurd rfl hpq
        · exact key q hq
        · exact (key p hp).symm
        · exact hM'disj p hp q hq hpq
    · refine ⟨∅, A.erase 0, erase_subset _ _, ?_, ?_, by simp, by simp, by simp⟩
      · intro x hx y hy hxy
        rw [mem_erase] at hx hy hxy
        refine hA ⟨x, hx.2, y, hy.2, hxy.2, hx.1, hy.1, ?_⟩
        rintro rfl
        exact hxy.1 (charTwo_add_self x)
      · have : A \ A.erase 0 ⊆ {0} := by
          intro v hv
          simp only [mem_sdiff, mem_erase] at hv
          simp only [mem_singleton]
          by_contra h
          exact hv.2 ⟨h, hv.1⟩
        simpa using card_le_card this

/-! #### Constants and potential of the pruning argument -/

/-- The exponent `γ₀ = log₂ (72/35)`, so that `2 ^ γ₀ = 4 / (35/18)`. -/
private noncomputable def γ₀ : ℝ := Real.logb 2 (72 / 35)

private lemma two_rpow_γ₀ : (2 : ℝ) ^ γ₀ = 72 / 35 :=
  Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

private lemma one_lt_γ₀ : 1 < γ₀ := by
  rw [γ₀, Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num), Real.rpow_one]
  norm_num

private lemma γ₀_lt_two : γ₀ < 2 := by
  rw [γ₀, Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
  norm_num

/-- `a₀ = 1 - 1/γ₀`, the exponent of the potential. -/
private noncomputable def a₀ : ℝ := 1 - 1 / γ₀

private lemma a₀_pos : 0 < a₀ := by
  have := one_lt_γ₀
  rw [a₀, sub_pos, div_lt_one (by linarith)]
  exact this

private lemma a₀_le_half : a₀ ≤ 1 / 2 := by
  have h1 := one_lt_γ₀
  have h2 := γ₀_lt_two
  have : 1 / 2 ≤ 1 / γ₀ := one_div_le_one_div_of_le (by linarith) h2.le
  rw [a₀]
  linarith

/-- The pruning threshold. -/
private noncomputable def τ₀ (n : ℕ) (T : ℕ) : ℝ :=
  1 / 144 * 2 ^ n * ((T : ℝ) / ((2 : ℝ) ^ n) ^ 2) ^ (1 / γ₀)

/-- The potential. -/
private noncomputable def P₀ (n : ℕ) (T : ℕ) : ℝ :=
  2 ^ n / (a₀ * (1 / 144)) * ((T : ℝ) / ((2 : ℝ) ^ n) ^ 2) ^ a₀

/-- Each pruning step lowers the potential by at least `1` (Bernoulli's inequality for the
concave power `a ≤ 1`). -/
private lemma potential_step (N a κ g : ℝ) (hN : 0 < N) (ha0 : 0 < a) (ha1 : a ≤ 1) (hκ : 0 < κ)
    (hg : a - 1 + g = 0) (T D : ℝ) (hD : 0 < D) (hDT : D ≤ T)
    (hτ : κ * N * (T / N ^ 2) ^ g ≤ D) :
    N / (a * κ) * ((T - D) / N ^ 2) ^ a + 1 ≤ N / (a * κ) * (T / N ^ 2) ^ a := by
  have hN2 : 0 < N ^ 2 := by positivity
  set x := T / N ^ 2 with hx
  set y := (T - D) / N ^ 2 with hy
  have hxpos : 0 < x := div_pos (by linarith) hN2
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hN2.le
  have hxy : x - y = D / N ^ 2 := by rw [hx, hy]; ring
  have hyx : 0 ≤ y / x := div_nonneg hy0 hxpos.le
  have hb := rpow_one_add_le_one_add_mul_self (s := y / x - 1) (by linarith) ha0.le ha1
  rw [add_sub_cancel, Real.div_rpow hy0 hxpos.le] at hb
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hxpos a
  have h1 : y ^ a ≤ x ^ a + a * (x ^ a * (y / x - 1)) := by
    have := mul_le_mul_of_nonneg_left hb hxa.le
    rw [mul_div_cancel₀ _ hxa.ne'] at this
    linarith
  have h2 : x ^ a * (y / x - 1) = - (x ^ (a - 1) * (x - y)) := by
    rw [Real.rpow_sub_one hxpos.ne']
    field_simp
    ring
  have h3 : κ * x ^ g / N ≤ x - y := by
    rw [hxy, div_le_div_iff₀ hN hN2]
    nlinarith
  have h4 : x ^ (a - 1) * x ^ g = 1 := by
    rw [← Real.rpow_add hxpos, hg, Real.rpow_zero]
  have hxa1 : 0 < x ^ (a - 1) := Real.rpow_pos_of_pos hxpos _
  have h5 : y ^ a ≤ x ^ a - a * κ / N := by
    calc y ^ a ≤ x ^ a - a * (x ^ (a - 1) * (x - y)) := by rw [h2] at h1; linarith
      _ ≤ x ^ a - a * (x ^ (a - 1) * (κ * x ^ g / N)) := by gcongr
      _ = x ^ a - a * κ / N := by
        rw [show x ^ (a - 1) * (κ * x ^ g / N) = κ * (x ^ (a - 1) * x ^ g) / N by ring, h4]
        ring
  have hc : 0 < N / (a * κ) := by positivity
  calc N / (a * κ) * y ^ a + 1 ≤ N / (a * κ) * (x ^ a - a * κ / N) + 1 := by gcongr
    _ = N / (a * κ) * x ^ a := by field_simp; ring

private lemma P₀_step (n : ℕ) :
    ∀ T D : ℕ, 0 < D → D ≤ T → τ₀ n T ≤ D → P₀ n (T - D) + 1 ≤ P₀ n T := by
  intro T D hD hDT hτ
  have h := potential_step (2 ^ n) a₀ (1 / 144) (1 / γ₀) (by positivity) a₀_pos
    (by linarith [a₀_le_half]) (by norm_num) (by rw [a₀]; ring) T D (by exact_mod_cast hD)
    (by exact_mod_cast hDT) hτ
  simp only [P₀]
  rw [Nat.cast_sub hDT]
  exact h

private lemma P₀_nonneg (n T : ℕ) : 0 ≤ P₀ n T := by
  have := a₀_pos
  unfold P₀
  positivity

/-- The final contradiction: `12 < E u ^ (1/γ)` and `u E ^ γ ≤ 12` are incompatible for
`γ > 1`. -/
private lemma false_of_rpow_bounds (γ : ℝ) (hγ : 1 < γ) (E u : ℝ) (hE : 0 < E) (hu : 0 < u)
    (h1 : 12 < E * u ^ (1 / γ)) (h2 : u * E ^ γ ≤ 12) : False := by
  have hγ0 : 0 < γ := by linarith
  have h3 : (12 : ℝ) ^ γ < (E * u ^ (1 / γ)) ^ γ := Real.rpow_lt_rpow (by norm_num) h1 hγ0
  rw [Real.mul_rpow hE.le (Real.rpow_nonneg hu.le _), ← Real.rpow_mul hu.le, one_div,
    inv_mul_cancel₀ hγ0.ne', Real.rpow_one] at h3
  have h4 : (12 : ℝ) < 12 ^ γ := by
    calc (12 : ℝ) = 12 ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < 12 ^ γ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hγ
  linarith

private lemma triS_card_le_sq {n : ℕ} (X Y Z S : Finset (Fin n → ZMod 2)) :
    ((triS X Y Z S).card : ℝ) ≤ ((2 : ℝ) ^ n) ^ 2 := by
  have h1 : (triS X Y Z S).card ≤ ((X ∩ S) ×ˢ (Y ∩ S)).card := card_filter_le _ _
  have h2 : ((X ∩ S) ×ˢ (Y ∩ S)).card ≤ 2 ^ n * 2 ^ n := by
    rw [card_product]
    have hc : ∀ U : Finset (Fin n → ZMod 2), U.card ≤ 2 ^ n := by
      intro U
      have := card_le_univ U
      simpa [Fintype.card_fun, ZMod.card] using this
    exact Nat.mul_le_mul (hc _) (hc _)
  have : ((triS X Y Z S).card : ℝ) ≤ (2 ^ n * 2 ^ n : ℕ) := by exact_mod_cast h1.trans h2
  rw [sq]
  exact_mod_cast this

/-- A configuration with at least one triangle in which every positive degree is below the
threshold `τ₀` contradicts the random-kernel bound `card_tri_le`. -/
private theorem false_of_degS_lt {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hX0 : (0 : Fin n → ZMod 2) ∉ X) (hY0 : (0 : Fin n → ZMod 2) ∉ Y)
    (S' : Finset (Fin n → ZMod 2))
    (ht : 0 < (triS X Y Z S').card)
    (hdeg : ∀ v, 0 < degS X Y Z S' v → (degS X Y Z S' v : ℝ) < τ₀ n (triS X Y Z S').card) :
    False := by
  classical
  set t := (triS X Y Z S').card with ht_def
  set Δ := (univ : Finset (Fin n → ZMod 2)).sup (degS X Y Z S') with hΔ_def
  have hle : ∀ v, degS X Y Z S' v ≤ Δ := fun v => le_sup (mem_univ v)
  obtain ⟨v₀, -, hv₀⟩ :=
    exists_mem_eq_sup (univ : Finset (Fin n → ZMod 2)) univ_nonempty (degS X Y Z S')
  have hΔ1 : 1 ≤ Δ := by
    obtain ⟨q, hq⟩ := card_pos.mp ht
    have : 0 < degS X Y Z S' q.1 := card_pos.mpr ⟨q, mem_filter.mpr ⟨hq, Or.inl rfl⟩⟩
    exact this.trans_le (hle _)
  have hΔτ : (Δ : ℝ) < τ₀ n t := by
    have h0 : 0 < degS X Y Z S' v₀ := by rw [← hv₀]; omega
    have := hdeg v₀ h0
    rw [← hv₀] at this
    exact this
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have htN := triS_card_le_sq X Y Z S'
  have hu1 : (t : ℝ) / ((2 : ℝ) ^ n) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact htN
  have hupos : (0 : ℝ) < (t : ℝ) / ((2 : ℝ) ^ n) ^ 2 := by
    have : (0 : ℝ) < t := by exact_mod_cast ht
    positivity
  have hτN : τ₀ n t ≤ 1 / 144 * 2 ^ n := by
    unfold τ₀
    have : ((t : ℝ) / ((2 : ℝ) ^ n) ^ 2) ^ (1 / γ₀) ≤ 1 :=
      Real.rpow_le_one hupos.le hu1 (by have := one_lt_γ₀; positivity)
    have h144 : (0 : ℝ) ≤ 1 / 144 * 2 ^ n := by positivity
    calc 1 / 144 * 2 ^ n * ((t : ℝ) / ((2 : ℝ) ^ n) ^ 2) ^ (1 / γ₀)
        ≤ 1 / 144 * 2 ^ n * 1 := by gcongr
      _ = 1 / 144 * 2 ^ n := mul_one _
  have h6 : 6 * Δ ≤ 2 ^ n := by
    have : ((6 * Δ : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this.le
  have hex : ∃ r, 6 * Δ ≤ 2 ^ r := ⟨n, h6⟩
  set r := Nat.find hex with hr_def
  have hr6 : 6 * Δ ≤ 2 ^ r := Nat.find_spec hex
  have hrn : r ≤ n := Nat.find_min' hex h6
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, pow_zero] at hr6
    omega
  obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero hr0
  have hr'6 : ¬ 6 * Δ ≤ 2 ^ r' := Nat.find_min hex (by omega)
  have h12 : 2 ^ r < 12 * Δ := by rw [hr', pow_succ]; omega
  have hL5 := card_tri_le (X ∩ S') (Y ∩ S') (Z ∩ S')
    (hXY.mono inter_subset_left inter_subset_left) (hXZ.mono inter_subset_left inter_subset_left)
    (hYZ.mono inter_subset_left inter_subset_left) (fun h => hX0 (mem_inter.mp h).1)
    (fun h => hY0 (mem_inter.mp h).1) Δ r hrn hr6 hle
  change (t : ℝ) ≤ 12 * 4 ^ r * (35 / 18 : ℝ) ^ (n - r) at hL5
  set E : ℝ := 2 ^ (n - r) with hE_def
  have hE : 0 < E := by positivity
  have hNE : (2 : ℝ) ^ n = 2 ^ r * E := by rw [hE_def, ← pow_add]; congr 1; omega
  have hβE : (35 / 18 : ℝ) ^ (n - r) * E ^ γ₀ = 4 ^ (n - r) := by
    have : E ^ γ₀ = (72 / 35 : ℝ) ^ (n - r) := by
      rw [hE_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), two_rpow_γ₀, Real.rpow_natCast]
    rw [this, ← mul_pow]
    norm_num
  have hN2 : ((2 : ℝ) ^ n) ^ 2 = 4 ^ r * 4 ^ (n - r) := by
    rw [← pow_mul, mul_comm, pow_mul, ← pow_add]
    norm_num
    omega
  set u : ℝ := (t : ℝ) / ((2 : ℝ) ^ n) ^ 2 with hu_def
  apply false_of_rpow_bounds γ₀ one_lt_γ₀ E u hE hupos
  · have h1 : ((2 : ℝ) ^ r) < 12 * Δ := by exact_mod_cast h12
    have h2 : (2 : ℝ) ^ r < 12 * τ₀ n t := by linarith
    have h3 : 12 * τ₀ n t = 2 ^ r * (E * u ^ (1 / γ₀)) / 12 := by
      have : τ₀ n t = 1 / 144 * 2 ^ n * u ^ (1 / γ₀) := rfl
      rw [this, hNE]
      ring
    rw [h3] at h2
    have h2r : (0 : ℝ) < 2 ^ r := by positivity
    by_contra hcon
    push Not at hcon
    have : 2 ^ r * (E * u ^ (1 / γ₀)) / 12 ≤ 2 ^ r := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  · rw [hu_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity), hN2]
    have hEg : 0 ≤ E ^ γ₀ := Real.rpow_nonneg hE.le _
    calc (t : ℝ) * E ^ γ₀ ≤ 12 * 4 ^ r * (35 / 18 : ℝ) ^ (n - r) * E ^ γ₀ := by gcongr
      _ = 12 * (4 ^ r * 4 ^ (n - r)) := by rw [mul_assoc (12 * 4 ^ r), hβE]; ring

/-- `m` pairwise vertex-disjoint triangles force at least
`(a₀ m / (288 · 2 ^ n)) ^ (1/a₀) · 4 ^ n` triangles. -/
private theorem card_tri_ge {n : ℕ} (X Y Z : Finset (Fin n → ZMod 2))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hX0 : (0 : Fin n → ZMod 2) ∉ X) (hY0 : (0 : Fin n → ZMod 2) ∉ Y)
    (M : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hM : M ⊆ tri X Y Z) (hdisj : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → Disjoint (verts p) (verts q)) :
    (a₀ * (1 / 144) * M.card / (2 * 2 ^ n)) ^ (1 / a₀) * ((2 : ℝ) ^ n) ^ 2 ≤
      ((tri X Y Z).card : ℝ) := by
  classical
  have ha := a₀_pos
  rcases Nat.eq_zero_or_pos M.card with hm | hm
  · rw [hm, Nat.cast_zero, mul_zero, zero_div, Real.zero_rpow (by positivity)]
    simp
  have hS₀ : triS X Y Z (X ∪ Y ∪ Z) = tri X Y Z := by
    simp only [triS]
    congr 1
    · exact inter_eq_left.mpr (subset_union_left.trans subset_union_left)
    · exact inter_eq_left.mpr (subset_union_right.trans subset_union_left)
    · exact inter_eq_left.mpr subset_union_right
  obtain ⟨S', -, hS'deg, hS'card⟩ := exists_pruned X Y Z (τ₀ n) (P₀ n) (P₀_step n) (X ∪ Y ∪ Z)
  rw [hS₀] at hS'card
  have hsurv := card_le_card_triS_add X Y Z M hM hdisj S'
  by_contra hlt
  push Not at hlt
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hN2 : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 2 := by positivity
  have hmR : (0 : ℝ) < M.card := by exact_mod_cast hm
  have hbase : 0 ≤ a₀ * (1 / 144) * M.card / (2 * 2 ^ n) := by positivity
  have hP : P₀ n (tri X Y Z).card < M.card / 2 := by
    have h1 : ((tri X Y Z).card : ℝ) / ((2 : ℝ) ^ n) ^ 2 <
        (a₀ * (1 / 144) * M.card / (2 * 2 ^ n)) ^ (1 / a₀) := by
      rw [div_lt_iff₀ hN2]
      exact hlt
    have h2 := Real.rpow_lt_rpow (by positivity) h1 ha
    rw [← Real.rpow_mul hbase, one_div_mul_cancel ha.ne', Real.rpow_one] at h2
    unfold P₀
    calc 2 ^ n / (a₀ * (1 / 144)) * (((tri X Y Z).card : ℝ) / ((2 : ℝ) ^ n) ^ 2) ^ a₀
        < 2 ^ n / (a₀ * (1 / 144)) * (a₀ * (1 / 144) * M.card / (2 * 2 ^ n)) := by gcongr
      _ = M.card / 2 := by field_simp
  have hP' := P₀_nonneg n (triS X Y Z S').card
  have hk : (((X ∪ Y ∪ Z) \ S').card : ℝ) < M.card / 2 := by linarith
  have hsR : (M.card : ℝ) ≤ (triS X Y Z S').card + ((X ∪ Y ∪ Z) \ S').card := by
    exact_mod_cast hsurv
  have ht' : 0 < (triS X Y Z S').card := by
    have : (0 : ℝ) < (triS X Y Z S').card := by linarith
    exact_mod_cast this
  exact false_of_degS_lt X Y Z hXY hXZ hYZ hX0 hY0 S' ht' hS'deg

/-- **Polynomial triangle removal holds in $\mathbb{F}_2^n$.** There are real constants $c > 0$
and $C > 0$ such that for every natural number $n$, every finite set $A \subseteq \mathbb{F}_2^n$
and every real number $\varepsilon$ with $0 < \varepsilon \le 1$ the following holds: if every
triangle-free $B \subseteq A$ misses at least $\varepsilon 2^n$ elements of $A$, then the
triangle count of $A$ is at least $c \varepsilon^C 4^n$. Here a set $B \subseteq \mathbb{F}_2^n$
is triangle-free when there are no $x, y \in B$ with $x + y \in B$ (the case $x = y$ is allowed),
and the triangle count of $A$ is the number of ordered pairs $(x, y) \in A \times A$ with
$x + y \in A$, so that it divided by $4^n$ is the probability that $x, y, x + y \in A$ for
independent uniform $x, y \in \mathbb{F}_2^n$.

This answers O'Donnell's Problem 14 in the affirmative. Fox and Lovász proved it with the
essentially tight exponent $C = 1 + 1/(5/3 - \log_2 3) \approx 13.239$.

Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 14 (Triangle Removal in 𝔽₂ⁿ); resolution: J. Fox and L. M. Lovász, A tight bound for Green's
arithmetic triangle removal lemma in vector spaces, Adv. Math. 321 (2017), 287-297,
arXiv:1606.01230, Theorem 1: for 0 < ε < 1 and δ = (ε/3)^{C_p}, if X, Y, Z ⊆ 𝔽_pⁿ span fewer than δ
N² triangles (N = pⁿ) then removing εN elements of X ∪ Y ∪ Z kills all triangles; C₂ = 1 + 1/(5/3 -
log₂ 3) ≈ 13.239 (applied with X = Y = Z = A and p = 2; the case ε = 1 follows from ε < 1),
https://arxiv.org/abs/1606.01230.
-/
theorem polynomialTriangleRemoval_holds : polynomialTriangleRemoval := by
  have ha := a₀_pos
  have ha2 := a₀_le_half
  set c₁ : ℝ := (a₀ * (1 / 144) / 12) ^ (1 / a₀) with hc₁
  have hc₁pos : 0 < c₁ := by positivity
  refine ⟨min c₁ (1 / 4), 1 / a₀, lt_min hc₁pos (by norm_num), by positivity, ?_⟩
  intro n A ε hε0 hε1 hrem
  classical
  obtain ⟨M, B, hBA, hBfree, hcard, hMA, hMnd, hMdisj⟩ := exists_disjoint_triangles A
  have hεB := hrem B hBA hBfree
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have h4n : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hC2 : 2 ≤ 1 / a₀ := by
    rw [le_div_iff₀ ha]
    linarith
  by_cases hsmall : ε * 2 ^ n < 2
  · have hnf : ¬ IsTriangleFree A := by
      intro hA
      have h := hrem A (subset_refl _) hA
      simp only [sdiff_self, bot_eq_empty, card_empty, Nat.cast_zero] at h
      have : 0 < ε * 2 ^ n := mul_pos hε0 hN
      linarith
    have h1 : 1 ≤ triangleCount A := by
      unfold IsTriangleFree at hnf
      push Not at hnf
      obtain ⟨x, hx, y, hy, hxy⟩ := hnf
      exact card_pos.mpr ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hxy⟩⟩
    have h2 : ε ^ (1 / a₀) * 4 ^ n ≤ 4 := by
      rw [h4n]
      have h3 : ε ^ (1 / a₀) = ε ^ (1 / a₀ - 2) * ε ^ 2 := by
        rw [← Real.rpow_natCast ε 2, ← Real.rpow_add hε0]
        norm_num
      rw [h3]
      have h5 : ε ^ (1 / a₀ - 2) ≤ 1 := Real.rpow_le_one hε0.le hε1 (by linarith)
      have h6 : 0 ≤ ε ^ (1 / a₀ - 2) := Real.rpow_nonneg hε0.le _
      have h7 : (ε * 2 ^ n) ^ 2 ≤ 4 := by nlinarith [mul_pos hε0 hN]
      calc ε ^ (1 / a₀ - 2) * ε ^ 2 * ((2 : ℝ) ^ n) ^ 2
          = ε ^ (1 / a₀ - 2) * (ε * 2 ^ n) ^ 2 := by ring
        _ ≤ 1 * 4 := by gcongr
        _ = 4 := by ring
    have h8 : 0 ≤ ε ^ (1 / a₀) * 4 ^ n := by positivity
    calc min c₁ (1 / 4) * ε ^ (1 / a₀) * 4 ^ n ≤ 1 / 4 * (ε ^ (1 / a₀) * 4 ^ n) := by
          rw [mul_assoc]
          gcongr
          exact min_le_right _ _
      _ ≤ 1 / 4 * 4 := by gcongr
      _ = 1 := by norm_num
      _ ≤ triangleCount A := by exact_mod_cast h1
  · push Not at hsmall
    have hm : ε * 2 ^ n / 6 ≤ M.card := by
      have : ε * 2 ^ n ≤ 3 * M.card + 1 := by
        calc ε * 2 ^ n ≤ ((A \ B).card : ℝ) := hεB
          _ ≤ ((3 * M.card + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
          _ = 3 * M.card + 1 := by push_cast; ring
      linarith
    set X := M.image Prod.fst with hX
    set Y := M.image Prod.snd with hY
    set Z := M.image (fun p => p.1 + p.2) with hZ
    have hv1 : ∀ p : (Fin n → ZMod 2) × (Fin n → ZMod 2), p.1 ∈ verts p := by
      intro p; simp [verts]
    have hv2 : ∀ p : (Fin n → ZMod 2) × (Fin n → ZMod 2), p.2 ∈ verts p := by
      intro p; simp [verts]
    have hv3 : ∀ p : (Fin n → ZMod 2) × (Fin n → ZMod 2), p.1 + p.2 ∈ verts p := by
      intro p; simp [verts]
    have hXY : Disjoint X Y := by
      rw [disjoint_left]
      intro v hvX hvY
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hvX
      obtain ⟨q, hq, hqp⟩ := mem_image.mp hvY
      by_cases hpq : p = q
      · subst hpq
        exact (hMnd p hp).2.2 hqp.symm
      · exact disjoint_left.mp (hMdisj p hp q hq hpq) (hv1 p) (hqp ▸ hv2 q)
    have hXZ : Disjoint X Z := by
      rw [disjoint_left]
      intro v hvX hvZ
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hvX
      obtain ⟨q, hq, hqp⟩ := mem_image.mp hvZ
      by_cases hpq : p = q
      · subst hpq
        exact (hMnd p hp).2.1 (add_eq_left.mp hqp)
      · exact disjoint_left.mp (hMdisj p hp q hq hpq) (hv1 p) (hqp ▸ hv3 q)
    have hYZ : Disjoint Y Z := by
      rw [disjoint_left]
      intro v hvY hvZ
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hvY
      obtain ⟨q, hq, hqp⟩ := mem_image.mp hvZ
      by_cases hpq : p = q
      · subst hpq
        exact (hMnd p hp).1 (add_eq_right.mp hqp)
      · exact disjoint_left.mp (hMdisj p hp q hq hpq) (hv2 p) (hqp ▸ hv3 q)
    have hX0 : (0 : Fin n → ZMod 2) ∉ X := by
      intro h
      obtain ⟨p, hp, hp0⟩ := mem_image.mp h
      exact (hMnd p hp).1 hp0
    have hY0 : (0 : Fin n → ZMod 2) ∉ Y := by
      intro h
      obtain ⟨p, hp, hp0⟩ := mem_image.mp h
      exact (hMnd p hp).2.1 hp0
    have hMtri : M ⊆ tri X Y Z := by
      intro p hp
      simp only [tri, mem_filter, mem_product]
      exact ⟨⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩,
        mem_image_of_mem (fun p => p.1 + p.2) hp⟩
    have htc : (tri X Y Z).card ≤ triangleCount A := by
      apply card_le_card
      intro q hq
      simp only [tri, mem_filter, mem_product] at hq
      simp only [mem_filter, mem_product]
      obtain ⟨⟨h1, h2⟩, h3⟩ := hq
      obtain ⟨p1, hp1, e1⟩ := mem_image.mp h1
      obtain ⟨p2, hp2, e2⟩ := mem_image.mp h2
      obtain ⟨p3, hp3, e3⟩ := mem_image.mp h3
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← e1]; exact (hMA p1 hp1).1
      · rw [← e2]; exact (hMA p2 hp2).2.1
      · rw [← e3]; exact (hMA p3 hp3).2.2
    have hlow := card_tri_ge X Y Z hXY hXZ hYZ hX0 hY0 M hMtri hMdisj
    have hbase : a₀ * (1 / 144) * ε / 12 ≤ a₀ * (1 / 144) * M.card / (2 * 2 ^ n) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : 0 < a₀ * (1 / 144) := by positivity
      nlinarith
    calc min c₁ (1 / 4) * ε ^ (1 / a₀) * 4 ^ n ≤ c₁ * ε ^ (1 / a₀) * 4 ^ n := by
          gcongr
          exact min_le_left _ _
      _ = (a₀ * (1 / 144) * ε / 12) ^ (1 / a₀) * ((2 : ℝ) ^ n) ^ 2 := by
          rw [h4n, hc₁, ← Real.mul_rpow (by positivity) hε0.le]
          ring_nf
      _ ≤ (a₀ * (1 / 144) * M.card / (2 * 2 ^ n)) ^ (1 / a₀) * ((2 : ℝ) ^ n) ^ 2 := by
          gcongr
      _ ≤ (tri X Y Z).card := hlow
      _ ≤ triangleCount A := by exact_mod_cast htc

end MathlibExt.Combinatorics.TriangleRemovalVectorSpaceAMR127Problem0013Wanted
