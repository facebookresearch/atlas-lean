/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph
import MathlibExt.Analysis.Fourier.BooleanCube
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Chvátal's hereditary intersecting-family conjecture

The largest star in a hereditary family containing a nonempty set is at least as large as
every intersecting subfamily. We follow the spectral proof in Section 2 of Ellis, Filmus and
Friedgut, [Chvátal’s conjecture: a proof from The Book](https://arxiv.org/abs/2609.28404v2).

Source: Václav Chvátal's conjecture page
`https://users.encs.concordia.ca/~chvatal/conjecture.html` (also Erdős Problem 701).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ChvatalHereditaryIntersectingWanted

/-- **Hereditary families.** A finite family $F$ of finite subsets of $\alpha$ is hereditary (an
independence system) when it contains every subset of each of its members: if $A \in F$ and
$B \subseteq A$, then $B \in F$. -/
def IsHereditary {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B : Finset α, B ⊆ A → B ∈ F

/-- **Chvátal's conjecture.** The statement that for every finite set $X$ and every hereditary
family $F$ of subsets of $X$ that contains a nonempty set, there is a point $x \in X$ such that
every intersecting subfamily $G \subseteq F$ has at most as many members as the star
$\{A \in F : x \in A\}$ of $x$. Here $F$ is hereditary when it contains every subset of each of
its members, and $G$ is intersecting when any two distinct members of $G$ meet.

The point $x$ is fixed for the whole family, and the competing subfamilies $G$ need not be
hereditary. -/
def conjecture : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (F : Finset (Finset α)),
    IsHereditary F →
    (∃ A ∈ F, A.Nonempty) →
    ∃ x : α, ∀ G : Finset (Finset α),
      G ⊆ F → SetFamily.IsIntersecting G →
        G.card ≤ (F.filter (fun A => x ∈ A)).card

open Finset BooleanCube Matrix
open scoped symmDiff

variable {α : Type} [Fintype α] [DecidableEq α]

private noncomputable abbrev coeff (f : Finset α → ℝ) := fourierCoeff univ f

private noncomputable def signAt (S : Finset α) (i : α) : ℝ := if i ∈ S then -1 else 1

omit [Fintype α] in
private lemma char_prod (S T : Finset α) : fourierChar S T = ∏ i ∈ T, signAt S i := by
  classical
  simp [fourierChar, signAt, inter_comm]

omit [Fintype α] in
private lemma char_diff (X Y S : Finset α) :
    fourierChar (X ∆ Y) S = fourierChar S X * fourierChar S Y := by
  have comm (A B : Finset α) : fourierChar A B = fourierChar B A := by
    simp [fourierChar, inter_comm]
  rw [comm S X, comm S Y, char_prod, char_prod X, char_prod Y, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by
    by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [signAt, mem_symmDiff, hx, hy]

-- The Walsh multiplier with symbol h acts by convolution with its Fourier coefficients.
private lemma apply_kernel (h f : Finset α → ℝ) (X : Finset α) :
    ∑ Y, coeff h (X ∆ Y) * f Y = ∑ S, h S * fourierChar S X * coeff f S := by
  simp only [coeff, fourierCoeff, powerset_univ, card_univ, div_mul_eq_mul_div,
    ← Finset.sum_div, Finset.sum_mul, mul_div_assoc', Finset.mul_sum]
  rw [sum_comm]
  congr 1
  exact sum_congr rfl fun S _ => sum_congr rfl fun Y _ => by rw [char_diff]; ring

private noncomputable def face (A R B : Finset α) : ℝ :=
  if B ⊆ A then fourierChar R B else 0

-- On the face B ⊆ A, the character at R has no Fourier coefficient at S if
-- S and R disagree at even one coordinate in A.
private lemma face_coeff_zero (A R S : Finset α) {i : α} (hi : i ∈ A)
    (hd : ¬ (i ∈ R ↔ i ∈ S)) : coeff (face A R) S = 0 := by
  classical
  have hfilter : univ.filter (fun B : Finset α => B ⊆ A) = A.powerset := by ext; simp
  simp only [coeff, fourierCoeff, powerset_univ, face, ite_mul, zero_mul, ← sum_filter,
    hfilter, char_prod, ← prod_mul_distrib, ← prod_one_add]
  rw [prod_eq_zero hi, zero_div]
  by_cases hr : i ∈ R <;> by_cases hs : i ∈ S <;> simp_all [signAt]

private lemma face_eigenvector {F : Finset (Finset α)} (hF : IsHereditary F) {A : Finset α}
    (hA : A ∈ F) (h : Finset α → ℝ) (R : Finset α) (r : ℝ)
    (hr : ∀ S : Finset α, (∀ i ∈ A, i ∈ R ↔ i ∈ S) → h S = r) (X : Finset α) :
    ∑ Y ∈ F, coeff h (X ∆ Y) * face A R Y = r * face A R X := by
  classical
  rw [sum_subset (subset_univ F) (f := fun Y => coeff h (X ∆ Y) * face A R Y)
    (fun Y _ hY => by
      have hn : ¬ Y ⊆ A := fun hYA => hY (hF A hA Y hYA)
      simp [face, hn]), apply_kernel]
  conv_rhs => rw [fourier_inversion univ (face A R) X (by simp)]
  simp only [powerset_univ, mul_sum]
  apply sum_congr rfl
  intro S _
  by_cases hs : ∀ i ∈ A, i ∈ R ↔ i ∈ S
  · rw [hr S hs]
    ring
  · push Not at hs
    obtain ⟨i, hi, hne⟩ := hs
    have hz := face_coeff_zero A R S hi (by tauto)
    change _ = r * (coeff (face A R) S * fourierChar S X)
    simp [hz]

-- Evaluating a relation at a largest set with nonzero coefficient isolates that coefficient.
omit [Fintype α] in
private lemma faces_independent {F G : Finset (Finset α)} (hGF : G ⊆ F) (R : Finset α) :
    LinearIndependent ℝ (fun A : G => fun B : F => face A.val R B.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hi
  let supp := univ.filter (fun j => c j ≠ 0)
  obtain ⟨j, hj, hmax⟩ := exists_max_image supp (fun k : G => k.val.card)
    ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have he := congrFun hc (⟨j.val, hGF j.property⟩ : F)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
  rw [sum_eq_single j] at he
  · have hn : fourierChar R j.val ≠ 0 := by simp [fourierChar]
    simp [face, hn, (mem_filter.mp hj).2] at he
  · intro k _ hk
    by_cases hck : c k = 0
    · simp [hck]
    have hns : ¬ j.val ⊆ k.val := fun hsub => hk (Subtype.ext
      (eq_of_subset_of_card_le hsub (hmax k (mem_filter.mpr ⟨mem_univ _, hck⟩))).symm)
    simp [face, hns]
  · simp

private lemma eigenvalue_count {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (r : ℝ) (v : κ → ι → ℝ)
    (hv : LinearIndependent ℝ v) (he : ∀ k, M *ᵥ v k = r • v k) :
    Fintype.card κ ≤ (univ.filter (fun i => r = hM.eigenvalues i)).card := by
  classical
  let V := Module.End.eigenspace M.toLin' r
  let w (k : κ) : V := ⟨v k, Module.End.mem_eigenspace_iff.mpr (he k)⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp V.subtype hv
  have h := hw.fintype_card_le_finrank.trans (LinearMap.finrank_eigenspace_le M.toLin' r)
  rw [Matrix.charpoly_toLin', ← Polynomial.count_roots, hM.roots_charpoly_eq_eigenvalues,
    Multiset.count_map] at h
  exact h

-- The trace of M² is the sum of the squared eigenvalues. Each copy of ±1 contributes one.
private lemma spectral_lower {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (m : ℕ)
    (hm : ∀ r ∈ ({-1, 1} : Finset ℝ), m ≤ (univ.filter (fun i => r = hM.eigenvalues i)).card) :
    2 * (m : ℝ) ≤ ∑ i, ∑ j, (M i j) ^ 2 := by
  classical
  have hs (r : ℝ) (hr : r ∈ ({-1, 1} : Finset ℝ)) :
      (m : ℝ) ≤ ∑ i : ι, (if r = hM.eigenvalues i then (1 : ℝ) else 0) := by
    simpa using (Nat.cast_le (α := ℝ)).mpr (hm r hr)
  have ht : (M ^ 2).trace = ∑ i, (hM.eigenvalues i) ^ 2 := by
    conv_lhs => rw [hM.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
    simp [Matrix.diagonal_pow]
  have he : (M ^ 2).trace = ∑ i, ∑ j, (M i j) ^ 2 := by
    simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hM.isSymm.apply j i]
  rw [← he, ht]
  have hle : (∑ i : ι, ((if (-1 : ℝ) = hM.eigenvalues i then 1 else 0) +
      (if (1 : ℝ) = hM.eigenvalues i then 1 else 0))) ≤ ∑ i, (hM.eigenvalues i) ^ 2 := by
    apply sum_le_sum
    intro i _
    split_ifs <;> nlinarith [sq_nonneg (hM.eigenvalues i)]
  rw [sum_add_distrib] at hle
  linarith [hs (-1) (by simp), hs 1 (by simp)]

-- Translation by T exchanges the two sides of each coordinate i ∈ T.
omit [Fintype α] in
private lemma overlap_le (F : Finset (Finset α)) (T : Finset α) {i : α} (hi : i ∈ T) :
    (F.filter (fun X => X ∆ T ∈ F)).card ≤ 2 * (F.filter (fun X => i ∈ X)).card := by
  classical
  let Q := F.filter (fun X => X ∆ T ∈ F)
  have h₁ : (Q.filter (fun X => i ∈ X)).card ≤ (F.filter (fun X => i ∈ X)).card :=
    card_le_card (filter_subset_filter _ (filter_subset _ _))
  have h₂ : (Q.filter (fun X => i ∉ X)).card ≤ (F.filter (fun X => i ∈ X)).card := by
    apply card_le_card_of_injOn (fun X => X ∆ T)
    · intro X hX
      obtain ⟨hX, hn⟩ := mem_filter.mp hX
      exact mem_filter.mpr ⟨(mem_filter.mp hX).2, mem_symmDiff.mpr (Or.inr ⟨hi, hn⟩)⟩
    · intro X _ Y _ he
      simpa using congrArg (fun B : Finset α => B ∆ T) he
  have hcard := Q.card_filter_add_card_filter_not (fun X => i ∈ X)
  change Q.card ≤ _
  omega

private lemma spectral_upper (F : Finset (Finset α)) (h : Finset α → ℝ) (m : ℕ)
    (hm : ∀ i, (F.filter (fun X => i ∈ X)).card ≤ m)
    (hzero : coeff h ∅ = 0) (hsize : ∀ S, h S ^ 2 ≤ 1) :
    ∑ X ∈ F, ∑ Y ∈ F, coeff h (X ∆ Y) ^ 2 ≤ 2 * (m : ℝ) := by
  classical
  let w (T : Finset α) := coeff h T ^ 2
  -- Group the squared entries by the symmetric difference of the row and column.
  have hrow (X : Finset α) : ∑ Y ∈ F, w (X ∆ Y) = ∑ T, if X ∆ T ∈ F then w T else 0 := by
    let e : Finset α ≃ Finset α :=
      ⟨(X ∆ ·), (X ∆ ·), fun _ => symmDiff_symmDiff_cancel_left ..,
        fun _ => symmDiff_symmDiff_cancel_left ..⟩
    calc
      _ = ∑ Y, if Y ∈ F then w (X ∆ Y) else 0 := by simp
      _ = _ := Fintype.sum_equiv e _ _ (fun Y => by simp [e])
  have hw : ∑ T, w T ≤ 1 := by
    have hp := fourier_plancherel (univ : Finset α) h
    simp only [powerset_univ, card_univ] at hp
    change ∑ T, fourierCoeff univ h T ^ 2 ≤ 1
    rw [← hp, div_le_iff₀ (by positivity), one_mul]
    exact (sum_le_sum fun S _ => hsize S).trans_eq (by simp)
  change ∑ X ∈ F, ∑ Y ∈ F, w (X ∆ Y) ≤ _
  simp_rw [hrow]
  rw [sum_comm]
  calc
    _ ≤ ∑ T, 2 * (m : ℝ) * w T := by
      refine sum_le_sum fun T _ => ?_
      by_cases hT : T = ∅
      · simp [hT, w, hzero]
      obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hT
      have hc := (overlap_le F T hi).trans (Nat.mul_le_mul_left 2 (hm i))
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg _)
    _ ≤ _ := by rw [← mul_sum]; nlinarith

omit [Fintype α] in
private lemma intersecting_bound [Finite α] {F G : Finset (Finset α)}
    (hF : IsHereditary F) (hGF : G ⊆ F)
    (hG : ∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty) (m : ℕ)
    (hm : ∀ i, (F.filter (fun X => i ∈ X)).card ≤ m) : G.card ≤ m := by
  classical
  let := Fintype.ofFinite α
  -- Antisymmetrize the indicator of the upset generated by G.
  let u (S : Finset α) : ℝ := if ∃ A ∈ G, A ⊆ S then 1 else 0
  let h (S : Finset α) := u S - u Sᶜ
  have hanti (S : Finset α) : h Sᶜ = -h S := by simp [h]
  have hone {A S : Finset α} (hA : A ∈ G) (hAS : A ⊆ S) : h S = 1 := by
    have hn : ¬ ∃ B ∈ G, B ⊆ Sᶜ := by
      rintro ⟨B, hB, hBS⟩
      obtain ⟨i, hi⟩ := hG A hA B hB
      obtain ⟨hia, hib⟩ := mem_inter.mp hi
      exact (mem_compl.mp (hBS hib)) (hAS hia)
    simp [h, u, show ∃ A ∈ G, A ⊆ S from ⟨A, hA, hAS⟩, hn]
  have hzero : coeff h ∅ = 0 := by
    have hsum : ∑ S, u Sᶜ = ∑ S, u S :=
      Fintype.sum_equiv (⟨compl, compl, compl_compl, compl_compl⟩ : Finset α ≃ Finset α)
        _ _ (fun _ => rfl)
    simp [coeff, fourierCoeff, fourierChar, h, sum_sub_distrib, hsum]
  have hsize (S : Finset α) : h S ^ 2 ≤ 1 := by
    dsimp [h, u]
    split_ifs <;> norm_num
  let M : Matrix F F ℝ := fun X Y => coeff h (X.val ∆ Y.val)
  have hM : M.IsHermitian := Matrix.IsHermitian.ext fun X Y => by simp [M, symmDiff_comm]
  have countFaces (R : Finset α) (r : ℝ)
      (hr : ∀ A ∈ G, ∀ S : Finset α, (∀ i ∈ A, i ∈ R ↔ i ∈ S) → h S = r) :
      G.card ≤ (univ.filter (fun i => r = hM.eigenvalues i)).card := by
    rw [← Fintype.card_coe]
    apply eigenvalue_count hM r _ (faces_independent hGF R)
    intro A
    funext X
    change ∑ Y : F, coeff h (X.val ∆ Y.val) * face A.val R Y.val = _
    rw [sum_coe_sort F (fun Y => coeff h (X.val ∆ Y) * face A.val R Y)]
    exact
      face_eigenvector hF (hGF A.property) h R r (hr A A.property) X
  -- Each A in G contributes a face vector at each sign: untwisted at −1, parity-twisted at +1.
  have hl := spectral_lower hM G.card (by
    intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · apply countFaces ∅
      intro A hA S hs
      have hAS : A ⊆ Sᶜ := fun i hi => mem_compl.mpr fun his => (notMem_empty i) ((hs i hi).2 his)
      linarith [hone hA hAS, hanti S]
    · apply countFaces univ
      exact fun A hA S hs => hone hA (fun i hi => (hs i hi).1 (mem_univ i)))
  have hu := spectral_upper F h m hm hzero hsize
  have rows (X : Finset α) := sum_coe_sort F (fun Y => coeff h (X ∆ Y) ^ 2)
  simp only [M] at hl
  simp_rw [rows] at hl
  rw [sum_coe_sort F (fun X => ∑ Y ∈ F, coeff h (X ∆ Y) ^ 2)] at hl
  exact_mod_cast (show (G.card : ℝ) ≤ m by linarith)

/--
**Chvátal's conjecture holds.** For every finite set $X$ and every hereditary family $F$ of
subsets of $X$ (one containing every subset of each of its members) that contains a nonempty set,
there is a point $x \in X$ such that every intersecting subfamily $G \subseteq F$ (one in which
any two distinct members meet) has at most as many members as the star $\{A \in F : x \in A\}$.

Resolved true: Chang, Liu, and Liu (arXiv:2609.19123, 2026) prove Chvátal's conjecture. Ellis,
Filmus, and Friedgut (arXiv:2609.28404) give an independent spectral proof, and Keevash
(arXiv:2609.23595) proves the stronger Kahn flow conjecture. erdosproblems.com/701 lists the
Chang–Liu–Liu proof claim with a Lean formalization by Boon Suan Ho.

Source: Fan Chang, Hong
Liu, and Miao Liu, A proof of Chvátal's conjecture via a sharp correlation inequality,
arXiv:2609.19123 (2026), https://arxiv.org/abs/2609.19123; David Ellis, Yuval Filmus, and Ehud
Friedgut, Chvátal's conjecture: a proof from The Book, arXiv:2609.28404v2 (2026),
https://arxiv.org/abs/2609.28404; Peter Keevash, On Kahn's flow conjecture, arXiv:2609.23595
(2026), https://arxiv.org/abs/2609.23595. Moved from
`OpenConjectures/Combinatorics/ChvatalHereditaryIntersecting`.
-/
public theorem conjecture_holds : conjecture := by
  intro α _ _ F hF ⟨A, hA, a, ha⟩
  classical
  let size (i : α) := (F.filter (fun X => i ∈ X)).card
  obtain ⟨x, _, hx⟩ := exists_max_image univ size ⟨a, mem_univ _⟩
  have hmax (i : α) : size i ≤ size x := hx i (mem_univ i)
  refine ⟨x, fun G hGF hG => ?_⟩
  by_cases h₀ : ∅ ∈ G
  · have hsub : G ⊆ {∅} := by
      intro B hB
      by_contra hn
      have hne : B ≠ ∅ := by simpa using hn
      simpa using hG B hB ∅ h₀ hne
    have hpos : 0 < size a := card_pos.mpr ⟨A, mem_filter.mpr ⟨hA, ha⟩⟩
    exact (card_le_card hsub).trans ((card_singleton _).le.trans (hpos.trans_le (hmax a)))
  · apply intersecting_bound hF hGF _ (size x) hmax
    intro B hB C hC
    by_cases he : B = C
    · subst C
      simpa using nonempty_iff_ne_empty.mpr (fun he => h₀ (he ▸ hB))
    · exact hG B hB C hC he

end MathlibExt.Combinatorics.ChvatalHereditaryIntersectingWanted
