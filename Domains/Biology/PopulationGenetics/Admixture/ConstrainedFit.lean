/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.QpGraph
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Nonnegativity-constrained qpGraph edge-length fit

Maximize the qpGraph score `scoreS1 Q f (B *ᵥ l)` over edge lengths
`l ≥ 0`, for positive definite `Q` and arbitrary design matrix `B` (no
full-rank assumption). A constrained maximizer always exists; it is
characterized by the KKT conditions with gradient
`g = Bᵀ Q⁻¹ (f - B l)`: feasibility, `g ≤ 0` coordinatewise, and
complementary slackness `l e * g e = 0`. The fitted value `B *ᵥ l` is the
same for every maximizer, and `l` itself is unique when the Gram matrix
`Bᵀ Q⁻¹ B` is positive definite. The one-edge example `B = Q = 1, f = -1`
has the unique constrained maximizer `0`, where the unconstrained maximizer
`-1` is infeasible.

## Main results

* `QpGraph.IsConstrainedMaximizer`: the constrained maximization predicate.
* `QpGraph.exists_isConstrainedMaximizer`: existence for every positive
  definite `Q` and every `B`.
* `QpGraph.isConstrainedMaximizer_iff`: the KKT characterization.
* `QpGraph.mulVec_eq_of_isConstrainedMaximizer`,
  `QpGraph.eq_of_isConstrainedMaximizer_of_posDef_gram`: uniqueness of the
  fitted value, and of `l` under a positive definite Gram matrix.
* `QpGraph.isConstrainedMaximizer_one_neg`: the boundary example.

## References

* N. Patterson et al., "Ancient admixture in human history", *Genetics* 192
  (2012), 1065–1093 (qpGraph edge-length fitting with nonnegativity).
-/

@[expose] public section

open Matrix

namespace MathlibExt.Biology.PopulationGenetics.QpGraph

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

/-- `l` maximizes `scoreS1 Q f (B *ᵥ ·)` over the nonnegative orthant:
feasibility plus Mathlib's `IsMaxOn` predicate on `Set.Ici 0`. For singular `Q`,
the convention `Q⁻¹ = 0` makes the score `0`, so every `l ≥ 0` qualifies; the
intended `Q` is positive definite. -/
def IsConstrainedMaximizer (Q : Matrix ι ι ℝ) (B : Matrix ι E ℝ) (f : ι → ℝ)
    (l : E → ℝ) : Prop :=
  l ∈ Set.Ici 0 ∧ IsMaxOn (fun l => scoreS1 Q f (B *ᵥ l)) (Set.Ici 0) l

theorem isConstrainedMaximizer_iff_forall {Q : Matrix ι ι ℝ} (B : Matrix ι E ℝ) (f : ι → ℝ)
    {l : E → ℝ} :
    IsConstrainedMaximizer Q B f l ↔ (∀ e, 0 ≤ l e) ∧ ∀ l' : E → ℝ, (∀ e, 0 ≤ l' e) →
      scoreS1 Q f (B *ᵥ l') ≤ scoreS1 Q f (B *ᵥ l) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun e => Pi.le_def.mp h1 e,
      fun l' hl' => isMaxOn_iff.mp h2 l' (Pi.le_def.mpr hl')⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Pi.le_def.mpr h1,
      isMaxOn_iff.mpr fun l' hl' => h2 l' (fun e => Pi.le_def.mp hl' e)⟩

private theorem inv_transpose_eq_of_posDef {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) :
    (Q⁻¹)ᵀ = Q⁻¹ := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact hQ.inv.isHermitian.eq

private theorem quad_nonneg_of_posDef {n : Type*} [Fintype n] {M : Matrix n n ℝ}
    (hM : M.PosDef) (x : n → ℝ) : 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  have h := hM.posSemidef.dotProduct_mulVec_nonneg x
  simpa using h

private theorem quad_pos_of_posDef {n : Type*} [Fintype n] {M : Matrix n n ℝ}
    (hM : M.PosDef) {x : n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ (M *ᵥ x) := by
  have h := hM.dotProduct_mulVec_pos hx
  simpa using h

private theorem eq_zero_of_quad_eq_zero_of_posDef {n : Type*} [Fintype n]
    {M : Matrix n n ℝ} (hM : M.PosDef) {x : n → ℝ}
    (h : x ⬝ᵥ (M *ᵥ x) = 0) : x = 0 := by
  by_contra hx
  exact (ne_of_gt (quad_pos_of_posDef hM hx)) h

private theorem scoreS1_add {Q : Matrix ι ι ℝ} (hW : (Q⁻¹)ᵀ = Q⁻¹)
    (B : Matrix ι E ℝ) (f : ι → ℝ) (l d : E → ℝ) :
    scoreS1 Q f (B *ᵥ (l + d)) = scoreS1 Q f (B *ᵥ l) +
      d ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) -
      1 / 2 * ((B *ᵥ d) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ d))) := by
  set r := B *ᵥ l - f with hr
  set s := B *ᵥ d with hs
  have hadd : B *ᵥ (l + d) - f = r + s := by
    simp only [hr, hs, mulVec_add]
    abel
  have hsym : r ⬝ᵥ (Q⁻¹ *ᵥ s) = s ⬝ᵥ (Q⁻¹ *ᵥ r) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]
  have hcross : s ⬝ᵥ (Q⁻¹ *ᵥ r) = -(d ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l)))) := by
    have hsub : r = -(f - B *ᵥ l) := by simp only [hr]; abel
    rw [hsub, mulVec_neg, dotProduct_neg]
    congr 1
    rw [hs]
    exact (by rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
      dotProduct_comm] : (B *ᵥ d) ⬝ᵥ _ = d ⬝ᵥ (Bᵀ *ᵥ _))
  unfold scoreS1
  rw [hadd, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hsym, hcross]
  ring

private theorem improve_of_pos {t c C : ℝ} (ht : 0 < t) (hc : 0 < c)
    (h : t * C ≤ c) : 0 < t * c - 1 / 2 * (t ^ 2 * C) := by
  have hkey : 0 ≤ t * (c - t * C) := mul_nonneg ht.le (sub_nonneg.mpr h)
  have hpos : 0 < t * c := mul_pos ht hc
  nlinarith [hkey, hpos]

private theorem dir_dotProduct (e : E) [DecidableEq E] (g : E → ℝ) :
    (Pi.single e 1 : E → ℝ) ⬝ᵥ g = g e :=
  single_one_dotProduct e g

omit [Fintype ι] [DecidableEq ι] [Fintype E] in
private theorem dir_nonneg (e e' : E) [DecidableEq E] :
    0 ≤ (Pi.single e (1 : ℝ) : E → ℝ) e' := by
  by_cases h : e' = e
  · subst h
    rw [Pi.single_eq_same]
    exact zero_le_one
  · have h0 : (Pi.single e (1 : ℝ) : E → ℝ) e' = 0 := Pi.single_eq_of_ne h _
    rw [h0]

private theorem ker_gram_eq_ker {m n : Type*} [Fintype m] [Fintype n]
    {W : Matrix m m ℝ} (hW : W.PosDef) (B : Matrix m n ℝ) :
    LinearMap.ker (Bᵀ * W * B).mulVecLin = LinearMap.ker B.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    apply eq_zero_of_quad_eq_zero_of_posDef hW
    replace h := congr_arg (dotProduct x) h
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_transpose] at h
  · intro h
    rw [h, mulVec_zero, mulVec_zero]

private theorem rank_gram_eq {m n : Type*} [Fintype m] [Fintype n]
    {W : Matrix m m ℝ} (hW : W.PosDef) (B : Matrix m n ℝ) :
    (Bᵀ * W * B).rank = B.rank := by
  dsimp only [Matrix.rank]
  refine add_left_injective (Module.finrank ℝ (LinearMap.ker B.mulVecLin)) ?_
  dsimp only
  trans Module.finrank ℝ (LinearMap.range (Bᵀ * W * B).mulVecLin) +
    Module.finrank ℝ (LinearMap.ker (Bᵀ * W * B).mulVecLin)
  · rw [ker_gram_eq_ker hW B]
  · simp only [LinearMap.finrank_range_add_finrank_ker]

/-- The weighted normal equations `Bᵀ W B x = Bᵀ W f` are solvable for every `B`. -/
private theorem exists_normal_eq_sol {m n : Type*} [Fintype m] [Fintype n]
    {W : Matrix m m ℝ} (hW : W.PosDef) (B : Matrix m n ℝ) (f : m → ℝ) :
    ∃ x : n → ℝ, (Bᵀ * W * B) *ᵥ x = (Bᵀ * W) *ᵥ f := by
  have hle : LinearMap.range (Bᵀ * W * B).mulVecLin ≤ LinearMap.range Bᵀ.mulVecLin := by
    rw [Matrix.mul_assoc, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hrank : Module.finrank ℝ (LinearMap.range (Bᵀ * W * B).mulVecLin) =
      Module.finrank ℝ (LinearMap.range Bᵀ.mulVecLin) := by
    have h1 := rank_gram_eq hW B
    rw [← rank_transpose B] at h1
    exact h1
  have heq := Submodule.eq_of_le_of_finrank_eq hle hrank
  have hmem : (Bᵀ * W) *ᵥ f ∈ LinearMap.range (Bᵀ * W * B).mulVecLin := by
    rw [heq, ← mulVec_mulVec]
    exact LinearMap.mem_range.mpr ⟨W *ᵥ f, rfl⟩
  exact LinearMap.mem_range.mp hmem

/-- On the vectors supported in `S`, the score has an unconstrained maximizer `lh`, around
which the Pythagorean identity holds. -/
private theorem exists_face_center {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    {Q : Matrix m m ℝ} (hQ : Q.PosDef) (B : Matrix m n ℝ) (f : m → ℝ) (S : Finset n) :
    ∃ lh : n → ℝ, (∀ e, e ∉ S → lh e = 0) ∧ ∀ v : n → ℝ, (∀ e, e ∉ S → v e = 0) →
      scoreS1 Q f (B *ᵥ v) = scoreS1 Q f (B *ᵥ lh) -
        1 / 2 * ((B *ᵥ (v - lh)) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (v - lh)))) := by
  classical
  set d : n → ℝ := fun e => if e ∈ S then 1 else 0 with hd
  obtain ⟨y, hy⟩ := exists_normal_eq_sol hQ.inv (B * diagonal d) f
  have hdiag : ∀ v : n → ℝ, (∀ e, e ∉ S → v e = 0) → diagonal d *ᵥ v = v := by
    intro v hv
    funext e
    rw [mulVec_diagonal, hd]
    by_cases he : e ∈ S
    · simp [he]
    · simp [he, hv e he]
  refine ⟨diagonal d *ᵥ y, fun e he => by simp [mulVec_diagonal, hd, he], fun v hv => ?_⟩
  have h := scoreS1_eq_sub (inv_transpose_eq_of_posDef hQ) (B * diagonal d) f hy v
  simp only [← mulVec_mulVec] at h
  rw [mulVec_sub, hdiag v hv] at h
  exact h

/-- If the unconstrained maximizer `lh` on the face `S` has a negative coordinate, moving a
feasible point `l` of that face towards `lh` until a coordinate vanishes reaches a smaller face
without decreasing the score. -/
private theorem exists_smaller_face_le {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {Q : Matrix m m ℝ} (hQ : Q.PosDef) (B : Matrix m n ℝ) (f : m → ℝ)
    {S : Finset n} {lh : n → ℝ} (hlh0 : ∀ e, e ∉ S → lh e = 0)
    (hkey : ∀ v : n → ℝ, (∀ e, e ∉ S → v e = 0) →
      scoreS1 Q f (B *ᵥ v) = scoreS1 Q f (B *ᵥ lh) -
        1 / 2 * ((B *ᵥ (v - lh)) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (v - lh)))))
    {e₀ : n} (he₀ : lh e₀ < 0) {l : n → ℝ} (hl0 : ∀ e, 0 ≤ l e)
    (hlS : ∀ e, e ∉ S → l e = 0) :
    ∃ es ∈ S, ∃ l2 : n → ℝ, (∀ e, 0 ≤ l2 e) ∧ (∀ e, e ∉ S.erase es → l2 e = 0) ∧
      scoreS1 Q f (B *ᵥ l) ≤ scoreS1 Q f (B *ᵥ l2) := by
  have hneg_mem : ∀ e, lh e < 0 → e ∈ S := by
    intro e he
    by_contra h
    linarith [hlh0 e h]
  obtain ⟨es, hesN, hesmin⟩ := Finset.exists_min_image (S.filter fun e => lh e < 0)
    (fun e => l e / (l e - lh e)) ⟨e₀, Finset.mem_filter.mpr ⟨hneg_mem e₀ he₀, he₀⟩⟩
  obtain ⟨hesS, hes⟩ := Finset.mem_filter.mp hesN
  set t := l es / (l es - lh es) with ht
  have hden : 0 < l es - lh es := by linarith [hl0 es]
  have ht0 : 0 ≤ t := div_nonneg (hl0 es) hden.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
  have htes : t * (l es - lh es) = l es := div_mul_cancel₀ (l es) hden.ne'
  set l2 := l + t • (lh - l) with hl2
  have hl2e : ∀ e, l2 e = l e + t * (lh e - l e) := by
    intro e
    simp only [hl2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine ⟨es, hesS, l2, fun e => ?_, fun e he => ?_, ?_⟩
  · rw [hl2e]
    by_cases hneg : lh e < 0
    · have hmin : t ≤ l e / (l e - lh e) :=
        hesmin e (Finset.mem_filter.mpr ⟨hneg_mem e hneg, hneg⟩)
      have hden' : 0 < l e - lh e := by linarith [hl0 e]
      rw [le_div_iff₀ hden'] at hmin
      linarith
    · have hnn : 0 ≤ lh e := not_lt.mp hneg
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (hl0 e), mul_nonneg ht0 hnn]
  · rw [hl2e]
    by_cases hee : e = es
    · rw [hee]
      linear_combination -htes
    · have heS : e ∉ S := fun h => he (Finset.mem_erase.mpr ⟨hee, h⟩)
      rw [hlS e heS, hlh0 e heS]
      ring
  · have hl2S : ∀ e, e ∉ S → l2 e = 0 := by
      intro e he
      rw [hl2e, hlS e he, hlh0 e he]
      ring
    rw [hkey l hlS, hkey l2 hl2S]
    have hdiff : l2 - lh = (1 - t) • (l - lh) := by
      funext e
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hl2e]
      ring
    rw [hdiff]
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    have hq := quad_nonneg_of_posDef hQ.inv (B *ᵥ (l - lh))
    nlinarith [mul_nonneg hq ht0, mul_nonneg (mul_nonneg hq ht0) (sub_nonneg.mpr ht1)]

/-- A maximizer over the face of the orthant consisting of the vectors supported in `S`. -/
private theorem exists_max_on_face {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    {Q : Matrix m m ℝ} (hQ : Q.PosDef) (B : Matrix m n ℝ) (f : m → ℝ) (S : Finset n) :
    ∃ x : n → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ e, e ∉ S → x e = 0) ∧
      ∀ l : n → ℝ, (∀ e, 0 ≤ l e) → (∀ e, e ∉ S → l e = 0) →
        scoreS1 Q f (B *ᵥ l) ≤ scoreS1 Q f (B *ᵥ x) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    obtain ⟨lh, hlh0, hkey⟩ := exists_face_center hQ B f S
    by_cases hpos : ∀ e, 0 ≤ lh e
    · refine ⟨lh, hpos, hlh0, fun l _ hlS => ?_⟩
      rw [hkey l hlS]
      have hq := quad_nonneg_of_posDef hQ.inv (B *ᵥ (l - lh))
      linarith
    · obtain ⟨e₀, he₀⟩ := not_forall.mp hpos
      replace he₀ : lh e₀ < 0 := not_le.mp he₀
      have he₀S : e₀ ∈ S := by
        by_contra h
        linarith [hlh0 e₀ h]
      have ih' : ∀ e ∈ S, ∃ x : n → ℝ, (∀ e', 0 ≤ x e') ∧
          (∀ e', e' ∉ S.erase e → x e' = 0) ∧
          ∀ l : n → ℝ, (∀ e', 0 ≤ l e') → (∀ e', e' ∉ S.erase e → l e' = 0) →
            scoreS1 Q f (B *ᵥ l) ≤ scoreS1 Q f (B *ᵥ x) :=
        fun e he => ih (S.erase e) (Finset.erase_ssubset he)
      choose! mx hmx0 hmxS hmxmax using ih'
      obtain ⟨eb, hebS, hebmax⟩ :=
        Finset.exists_max_image S (fun e => scoreS1 Q f (B *ᵥ mx e)) ⟨e₀, he₀S⟩
      refine ⟨mx eb, hmx0 eb hebS,
        fun e he => hmxS eb hebS e (fun h => he (Finset.mem_of_mem_erase h)),
        fun l hl0 hlS => ?_⟩
      obtain ⟨es, hesS, l2, hl20, hl2S, hle⟩ :=
        exists_smaller_face_le hQ B f hlh0 hkey he₀ hl0 hlS
      have hbest : scoreS1 Q f (B *ᵥ mx es) ≤ scoreS1 Q f (B *ᵥ mx eb) := hebmax es hesS
      exact hle.trans ((hmxmax es hesS l2 hl20 hl2S).trans hbest)

/-- A constrained maximizer exists for every positive definite `Q`, with no
full-rank or coercivity assumption on `B`. -/
theorem exists_isConstrainedMaximizer {Q : Matrix ι ι ℝ} (hQ : Q.PosDef)
    (B : Matrix ι E ℝ) (f : ι → ℝ) :
    ∃ l : E → ℝ, IsConstrainedMaximizer Q B f l := by
  obtain ⟨x, hx0, -, hxmax⟩ := exists_max_on_face hQ B f Finset.univ
  exact ⟨x, (isConstrainedMaximizer_iff_forall B f).mpr
    ⟨hx0, fun l hl => hxmax l hl fun e he => absurd (Finset.mem_univ e) he⟩⟩

/-- KKT characterization with gradient `g = Bᵀ Q⁻¹ (f - B l)`, for positive
definite `Q`: a feasible `l` is a maximizer iff `g ≤ 0` coordinatewise and
`l e * g e = 0` for every `e`. -/
theorem isConstrainedMaximizer_iff {Q : Matrix ι ι ℝ} (hQ : Q.PosDef)
    (B : Matrix ι E ℝ) (f : ι → ℝ) {l : E → ℝ} :
    IsConstrainedMaximizer Q B f l ↔
      (∀ e, 0 ≤ l e) ∧ (∀ e, (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e ≤ 0) ∧
        ∀ e, l e * (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e = 0 := by
  have hW : (Q⁻¹)ᵀ = Q⁻¹ := inv_transpose_eq_of_posDef hQ
  rw [isConstrainedMaximizer_iff_forall]
  constructor
  · intro h
    obtain ⟨hfeas, hmax⟩ := h
    have hg : ∀ e, (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e ≤ 0 := by
      intro e
      by_contra hcon
      rw [not_le] at hcon
      let _ := Classical.typeDecidableEq E
      set u : E → ℝ := Pi.single e 1 with hu_def
      have hug : u ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) =
          (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e := dir_dotProduct e _
      have hu_nonneg : ∀ e', 0 ≤ u e' := fun e' => dir_nonneg e e'
      set C : ℝ := (B *ᵥ u) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ u)) with hC_def
      have hC : 0 ≤ C := by
        rw [hC_def]
        exact quad_nonneg_of_posDef hQ.inv _
      have hC1 : (0 : ℝ) < C + 1 := by linarith
      set t : ℝ := (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e / (C + 1) with ht_def
      have ht : 0 < t := by
        rw [ht_def]
        exact div_pos hcon hC1
      have htC : t * C ≤ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e := by
        rw [ht_def, div_mul_eq_mul_div, div_le_iff₀ hC1]
        nlinarith [hcon.le, hC]
      have hfeas' : ∀ e', 0 ≤ (l + t • u) e' := by
        intro e'
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h2 := mul_nonneg ht.le (hu_nonneg e')
        linarith [hfeas e']
      have hexp := scoreS1_add hW B f l (t • u)
      have hlin : (t • u) ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) =
          t * (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e := by
        rw [smul_dotProduct, hug, smul_eq_mul]
      have hquad : (B *ᵥ (t • u)) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (t • u))) = t ^ 2 * C := by
        simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          ← hC_def]
        ring
      have himp := hmax (l + t • u) hfeas'
      have hlt : scoreS1 Q f (B *ᵥ l) < scoreS1 Q f (B *ᵥ (l + t • u)) := by
        rw [hexp, hlin, hquad]
        have hcore := improve_of_pos ht hcon htC
        linarith
      exact absurd himp (not_le_of_gt hlt)
    refine ⟨hfeas, hg, ?_⟩
    intro e
    by_cases h0 : l e = 0
    · rw [h0, zero_mul]
    · have hpos : 0 < l e := (hfeas e).lt_of_ne (Ne.symm h0)
      have hge0 : (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e = 0 := by
        by_contra hcon
        have hneg : (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e < 0 :=
          lt_of_le_of_ne (hg e) hcon
        let _ := Classical.typeDecidableEq E
        set u : E → ℝ := Pi.single e 1 with hu_def
        have hug : u ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) =
            (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e := dir_dotProduct e _
        set C : ℝ := (B *ᵥ u) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ u)) with hC_def
        have hC : 0 ≤ C := by
          rw [hC_def]
          exact quad_nonneg_of_posDef hQ.inv _
        have hC1 : (0 : ℝ) < C + 1 := by linarith
        set b : ℝ := (-((Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e)) / (C + 1) with hb_def
        have hb : 0 < b := by
          rw [hb_def]
          exact div_pos (neg_pos.mpr hneg) hC1
        set t : ℝ := min (l e) b with ht_def
        have ht : 0 < t := by rw [ht_def]; exact lt_min hpos hb
        have ht_le_l : t ≤ l e := by rw [ht_def]; exact min_le_left _ _
        have ht_le_b : t ≤ b := by rw [ht_def]; exact min_le_right _ _
        have htC : t * C ≤ (-((Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e)) := by
          have hbC : b * C ≤ (-((Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e)) := by
            rw [hb_def, div_mul_eq_mul_div, div_le_iff₀ hC1]
            nlinarith [neg_pos.mpr hneg, hC]
          calc t * C ≤ b * C := mul_le_mul_of_nonneg_right ht_le_b hC
            _ ≤ (-((Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e)) := hbC
        have hfeas' : ∀ e', 0 ≤ (l + (-(t • u))) e' := by
          intro e'
          by_cases h : e' = e
          · rw [h]
            have h1 : (l + (-(t • u))) e = l e - t := by
              simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
                hu_def, Pi.single_eq_same, mul_one]
              ring
            rw [h1]
            linarith [ht_le_l]
          · have h0' : u e' = 0 := by
              rw [hu_def]
              exact Pi.single_eq_of_ne h _
            have h1 : (l + (-(t • u))) e' = l e' := by
              simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
                h0', mul_zero, neg_zero, add_zero]
            rw [h1]
            exact hfeas e'
        have hexp := scoreS1_add hW B f l (-(t • u))
        have hlin : (-(t • u)) ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) =
            t * (-((Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e)) := by
          rw [neg_dotProduct, smul_dotProduct, hug, smul_eq_mul]
          ring
        have hquad : (B *ᵥ (-(t • u))) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (-(t • u)))) =
            t ^ 2 * C := by
          simp only [mulVec_neg, neg_dotProduct, dotProduct_neg,
            mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← hC_def]
          ring
        have himp := hmax (l + (-(t • u))) hfeas'
        have hlt : scoreS1 Q f (B *ᵥ l) < scoreS1 Q f (B *ᵥ (l + (-(t • u)))) := by
          rw [hexp, hlin, hquad]
          have hcore := improve_of_pos ht (neg_pos.mpr hneg) htC
          linarith
        exact absurd himp (not_le_of_gt hlt)
      rw [hge0, mul_zero]
  · intro h
    obtain ⟨hfeas, hg, hcs⟩ := h
    refine ⟨hfeas, ?_⟩
    intro l' hl'
    have hexp := scoreS1_add hW B f l (l' - l)
    rw [add_sub_cancel] at hexp
    have hC : 0 ≤ (B *ᵥ (l' - l)) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (l' - l))) :=
      quad_nonneg_of_posDef hQ.inv _
    have hsub : (l' - l) ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) =
        l' ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) -
        l ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) :=
      sub_dotProduct _ _ _
    have hnonpos : l' ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) ≤ 0 := by
      unfold dotProduct
      exact Finset.sum_nonpos
        (fun e _ => mul_nonpos_of_nonneg_of_nonpos (hl' e) (hg e))
    have hzero : l ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) = 0 := by
      unfold dotProduct
      exact Finset.sum_eq_zero (fun e _ => hcs e)
    linarith [hexp, hC, hsub, hnonpos, hzero]

/-- For positive definite `Q`, the fitted value `B l` is the same for every
constrained maximizer. -/
theorem mulVec_eq_of_isConstrainedMaximizer {Q : Matrix ι ι ℝ} (hQ : Q.PosDef)
    {B : Matrix ι E ℝ} {f : ι → ℝ} {l₁ l₂ : E → ℝ}
    (h₁ : IsConstrainedMaximizer Q B f l₁) (h₂ : IsConstrainedMaximizer Q B f l₂) :
    B *ᵥ l₁ = B *ᵥ l₂ := by
  have hW : (Q⁻¹)ᵀ = Q⁻¹ := inv_transpose_eq_of_posDef hQ
  obtain ⟨hfeas₁, hmax₁⟩ := (isConstrainedMaximizer_iff_forall B f).mp h₁
  obtain ⟨hfeas₂, hmax₂⟩ := (isConstrainedMaximizer_iff_forall B f).mp h₂
  have kkt₁ := (isConstrainedMaximizer_iff hQ B f).mp h₁
  obtain ⟨_, hg₁, hcs₁⟩ := kkt₁
  have heq : scoreS1 Q f (B *ᵥ l₂) = scoreS1 Q f (B *ᵥ l₁) :=
    le_antisymm (hmax₁ l₂ hfeas₂) (hmax₂ l₁ hfeas₁)
  have hexp := scoreS1_add hW B f l₁ (l₂ - l₁)
  rw [add_sub_cancel] at hexp
  have hC : 0 ≤ (B *ᵥ (l₂ - l₁)) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (l₂ - l₁))) :=
    quad_nonneg_of_posDef hQ.inv _
  have hsub : (l₂ - l₁) ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l₁))) =
      l₂ ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l₁))) -
      l₁ ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l₁))) :=
    sub_dotProduct _ _ _
  have hnonpos : l₂ ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l₁))) ≤ 0 := by
    unfold dotProduct
    exact Finset.sum_nonpos
      (fun e _ => mul_nonpos_of_nonneg_of_nonpos (hfeas₂ e) (hg₁ e))
  have hzero : l₁ ⬝ᵥ (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l₁))) = 0 := by
    unfold dotProduct
    exact Finset.sum_eq_zero (fun e _ => hcs₁ e)
  have hC0 : (B *ᵥ (l₂ - l₁)) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (l₂ - l₁))) = 0 := by
    have hle : (B *ᵥ (l₂ - l₁)) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (l₂ - l₁))) ≤ 0 := by
      linarith [hexp, heq, hC, hsub, hnonpos, hzero]
    exact le_antisymm hle hC
  have hB0 : B *ᵥ (l₂ - l₁) = 0 := eq_zero_of_quad_eq_zero_of_posDef hQ.inv hC0
  have hsub2 : B *ᵥ (l₂ - l₁) = B *ᵥ l₂ - B *ᵥ l₁ := by simp only [mulVec_sub]
  rw [hsub2] at hB0
  exact (sub_eq_zero.mp hB0).symm

/-- For positive definite `Q`, when the Gram matrix `Bᵀ Q⁻¹ B` is positive
definite, the constrained maximizer `l` itself is unique: any two are equal. -/
theorem eq_of_isConstrainedMaximizer_of_posDef_gram {Q : Matrix ι ι ℝ}
    (hQ : Q.PosDef) {B : Matrix ι E ℝ} (hgram : (Bᵀ * Q⁻¹ * B).PosDef)
    {f : ι → ℝ} {l₁ l₂ : E → ℝ}
    (h₁ : IsConstrainedMaximizer Q B f l₁) (h₂ : IsConstrainedMaximizer Q B f l₂) :
    l₁ = l₂ := by
  have hB : B *ᵥ l₁ = B *ᵥ l₂ := mulVec_eq_of_isConstrainedMaximizer hQ h₁ h₂
  have hG0 : (Bᵀ * Q⁻¹ * B) *ᵥ (l₁ - l₂) = 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    have hBd : B *ᵥ (l₁ - l₂) = 0 := by
      simp only [mulVec_sub]
      rw [hB, sub_self]
    rw [hBd, mulVec_zero, mulVec_zero]
  have hdot : (l₁ - l₂) ⬝ᵥ ((Bᵀ * Q⁻¹ * B) *ᵥ (l₁ - l₂)) = 0 := by
    rw [hG0, dotProduct_zero]
  have hsub0 : l₁ - l₂ = 0 := eq_zero_of_quad_eq_zero_of_posDef hgram hdot
  exact sub_eq_zero.mp hsub0

/-- One-edge boundary example: with `B = Q = 1` and `f = -1`, the unique
constrained maximizer is `0` (the unconstrained maximizer `-1` is infeasible). -/
theorem isConstrainedMaximizer_one_neg :
    IsConstrainedMaximizer (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (-1 : ℝ)) 0 ∧
      ∀ l : Fin 1 → ℝ, IsConstrainedMaximizer (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (-1 : ℝ)) l → l = 0 := by
  have hscore : ∀ l : Fin 1 → ℝ,
      scoreS1 (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (-1 : ℝ))
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ l) = -(1 / 2) * (l 0 + 1) ^ 2 := by
    intro l
    unfold scoreS1
    simp [dotProduct]
    ring
  have h0val : scoreS1 (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (-1 : ℝ))
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ 0) = -(1 / 2) := by
    rw [hscore 0]
    simp
  have hall : ∀ l' : Fin 1 → ℝ, (∀ e, 0 ≤ l' e) →
      scoreS1 (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (-1 : ℝ))
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ l') ≤
      scoreS1 (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (-1 : ℝ))
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ 0) := by
    intro l' hl'
    rw [hscore l', h0val]
    have h0 : (0 : ℝ) ≤ l' 0 := hl' 0
    nlinarith [sq_nonneg (l' 0), h0]
  refine ⟨(isConstrainedMaximizer_iff_forall 1 (fun _ => (-1 : ℝ))).mpr ⟨fun e => le_rfl, hall⟩, ?_⟩
  intro l hl
  obtain ⟨hfeas, hmax⟩ := (isConstrainedMaximizer_iff_forall 1 (fun _ => (-1 : ℝ))).mp hl
  have h1 := hall l hfeas
  have h2 := hmax 0 (fun e => le_rfl)
  have heq := le_antisymm h1 h2
  rw [hscore l, h0val] at heq
  have h0 : (0 : ℝ) ≤ l 0 := hfeas 0
  have hsq : (l 0 + 1) ^ 2 = 1 := by linarith
  have hfact : l 0 * (l 0 + 2) = 0 := by linear_combination hsq
  have hne : l 0 + 2 ≠ 0 := by linarith
  have hl0 : l 0 = 0 := by
    rcases mul_eq_zero.mp hfact with h | h
    · exact h
    · exact absurd h hne
  funext i
  fin_cases i
  exact hl0

end MathlibExt.Biology.PopulationGenetics.QpGraph
