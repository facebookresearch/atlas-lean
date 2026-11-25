/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.GroebnerBasis

/-!
# Buchberger's criterion

A set `G` of nonzero polynomials is a Gröbner basis of the ideal it generates as soon as every
S-polynomial `S(g, h)`, `g, h ∈ G`, has a standard representation `∑_{b ∈ G} q_b b` in which no
summand has leading monomial above that of `S(g, h)`; this is what "S(g, h) reduces to zero
modulo G" provides. It is the hard direction of Buchberger's criterion and the correctness proof
of Buchberger's algorithm. The easy direction is
`MathlibExt.RingTheory.MvPolynomial.GroebnerBasis.IsGroebnerBasis.sPolynomial_remainder_eq_zero`.

## Proof

Write `f = ∑_b q_b b` and let `δ` bound the leading monomials of the summands `b q_b`. If the
coefficient of `x^δ` in `f` is nonzero, the leading monomial of `f` is `δ` and is divisible by the
leading monomial of a summand reaching `δ`. Otherwise the top terms cancel. If at least two
summands reach `δ`, the leading term of one of them is moved onto another through the identity
`c x^α g_i = (c lc(g_i) / lc(g_j)) x^{δ - deg g_j} g_j + (c / lc(g_j)) x^{δ - γ} S(g_i, g_j)`, whose
last term has a standard representation of degree below `δ`; this lowers the number of summands
reaching `δ`. When no summand reaches `δ`, the bound drops. Induction on the bound (a well-order)
and on the number of summands reaching it concludes.

Sources: D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6,
Theorem 6 (Buchberger's criterion) and §7 (Buchberger's algorithm, section only);
B. Hassett, *Math 465 Lecture Notes*, Brown University, 2002, Lecture 5, Theorem 5.2, whose proof
of `⇐` uses exactly the standard representations `S(f_i, f_j) = ∑ h_l f_l`, `LM(S) ≥ LM(h_l f_l)`,
and the double minimality on `x^δ` and on the number of summands reaching it followed here;
B. Buchberger, PhD thesis, Innsbruck, 1965.
-/

@[expose] public section

noncomputable section

namespace MathlibExt.RingTheory.MvPolynomial.BuchbergerCriterion

open _root_.MvPolynomial MonomialOrder MathlibExt.RingTheory.MvPolynomial.GroebnerBasis
open scoped MonomialOrder

variable {σ K : Type*} [Field K] (m : MonomialOrder σ)

/-- All monomials of `f` are at most `δ` for the monomial order. -/
private def LeDeg (δ : σ →₀ ℕ) (f : _root_.MvPolynomial σ K) : Prop :=
  ∀ d, m.toSyn δ < m.toSyn d → f.coeff d = 0

/-- All monomials of `f` are strictly below `δ` for the monomial order. -/
private def LtDeg (δ : σ →₀ ℕ) (f : _root_.MvPolynomial σ K) : Prop :=
  ∀ d, m.toSyn δ ≤ m.toSyn d → f.coeff d = 0

private theorem coeff_add (d : σ →₀ ℕ) (f g : _root_.MvPolynomial σ K) :
    (f + g).coeff d = f.coeff d + g.coeff d := by simp

private theorem coeff_zero' (d : σ →₀ ℕ) : (0 : _root_.MvPolynomial σ K).coeff d = 0 := by
  simp

variable {m}

private theorem LtDeg.leDeg {δ : σ →₀ ℕ} {f : _root_.MvPolynomial σ K} (h : LtDeg m δ f) :
    LeDeg m δ f := fun d hd ↦ h d hd.le

private theorem leDeg_zero (δ : σ →₀ ℕ) : LeDeg m δ (0 : _root_.MvPolynomial σ K) :=
  fun _ _ ↦ by simp

private theorem ltDeg_zero (δ : σ →₀ ℕ) : LtDeg m δ (0 : _root_.MvPolynomial σ K) :=
  fun _ _ ↦ by simp

private theorem LeDeg.add {δ : σ →₀ ℕ} {f g : _root_.MvPolynomial σ K} (hf : LeDeg m δ f)
    (hg : LeDeg m δ g) : LeDeg m δ (f + g) := fun d hd ↦ by
  simp [hf d hd, hg d hd]

private theorem LeDeg.sub {δ : σ →₀ ℕ} {f g : _root_.MvPolynomial σ K} (hf : LeDeg m δ f)
    (hg : LeDeg m δ g) : LeDeg m δ (f - g) := fun d hd ↦ by
  simp [hf d hd, hg d hd]

private theorem LtDeg.add {δ : σ →₀ ℕ} {f g : _root_.MvPolynomial σ K} (hf : LtDeg m δ f)
    (hg : LtDeg m δ g) : LtDeg m δ (f + g) := fun d hd ↦ by
  simp [hf d hd, hg d hd]

private theorem LtDeg.sub {δ : σ →₀ ℕ} {f g : _root_.MvPolynomial σ K} (hf : LtDeg m δ f)
    (hg : LtDeg m δ g) : LtDeg m δ (f - g) := fun d hd ↦ by
  simp [hf d hd, hg d hd]

private theorem LtDeg.mono {δ δ' : σ →₀ ℕ} {f : _root_.MvPolynomial σ K} (hf : LeDeg m δ f)
    (h : m.toSyn δ < m.toSyn δ') : LtDeg m δ' f := fun d hd ↦ hf d (h.trans_le hd)

/-- A product of polynomials bounded by `δ₁` and `δ₂` is bounded by `δ₁ + δ₂`. -/
private theorem LeDeg.mul {δ₁ δ₂ : σ →₀ ℕ} {f g : _root_.MvPolynomial σ K} (hf : LeDeg m δ₁ f)
    (hg : LeDeg m δ₂ g) : LeDeg m (δ₁ + δ₂) (f * g) := by
  classical
  intro d hd
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases h1 : m.toSyn x.1 ≤ m.toSyn δ₁
  · by_cases h2 : m.toSyn x.2 ≤ m.toSyn δ₂
    · exfalso
      have := add_le_add h1 h2
      rw [← map_add, ← map_add, hx] at this
      exact absurd hd (not_lt.2 this)
    · rw [hg _ (not_le.1 h2), mul_zero]
  · rw [hf _ (not_le.1 h1), zero_mul]

/-- A product of a polynomial bounded by `δ₁` and one strictly below `δ₂` is strictly below
`δ₁ + δ₂`. -/
private theorem LtDeg.mul {δ₁ δ₂ : σ →₀ ℕ} {f g : _root_.MvPolynomial σ K} (hf : LeDeg m δ₁ f)
    (hg : LtDeg m δ₂ g) : LtDeg m (δ₁ + δ₂) (f * g) := by
  classical
  intro d hd
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases h1 : m.toSyn x.1 ≤ m.toSyn δ₁
  · by_cases h2 : m.toSyn x.2 < m.toSyn δ₂
    · exfalso
      have := add_lt_add_of_le_of_lt h1 h2
      rw [← map_add, ← map_add, hx] at this
      exact absurd hd (not_le.2 this)
    · rw [hg _ (not_lt.1 h2), mul_zero]
  · rw [hf _ (not_le.1 h1), zero_mul]

private theorem leDeg_degree (f : _root_.MvPolynomial σ K) : LeDeg m (m.degree f) f := by
  intro d hd
  by_contra h
  exact absurd (m.le_degree (mem_support_iff.2 h)) (not_le.2 hd)

private theorem leDeg_monomial (d : σ →₀ ℕ) (c : K) : LeDeg m d (monomial d c) := by
  classical
  intro e he
  have hne : d ≠ e := by rintro rfl; exact lt_irrefl _ he
  simp [coeff_monomial, hne]

/-- Removing the leading term leaves a polynomial strictly below the leading monomial. -/
private theorem ltDeg_sub_leadingTerm (f : _root_.MvPolynomial σ K) :
    LtDeg m (m.degree f) (f - monomial (m.degree f) (m.leadingCoeff f)) := by
  classical
  intro d hd
  rcases hd.lt_or_eq with hlt | heq
  · have hne : m.degree f ≠ d := by rintro rfl; exact lt_irrefl _ hlt
    simp [coeff_monomial, hne, leDeg_degree f d hlt]
  · have := m.toSyn.injective heq
    subst this
    simp [leadingCoeff]

/-- Bounded by `δ` and with no `x^δ` term means strictly below `δ`. -/
private theorem ltDeg_of_leDeg_of_coeff {δ : σ →₀ ℕ} {f : _root_.MvPolynomial σ K}
    (hf : LeDeg m δ f) (h0 : f.coeff δ = 0) : LtDeg m δ f := by
  intro d hd
  rcases hd.lt_or_eq with hlt | heq
  · exact hf d hlt
  · rw [← m.toSyn.injective heq, h0]

/-- Bounded by `δ` with a nonzero `x^δ` term means leading monomial `δ`. -/
private theorem degree_eq_of_leDeg {δ : σ →₀ ℕ} {f : _root_.MvPolynomial σ K}
    (hf : LeDeg m δ f) (h0 : f.coeff δ ≠ 0) : m.degree f = δ := by
  apply m.toSyn.injective
  apply le_antisymm
  · by_contra h
    exact (m.coeff_degree_ne_zero_iff.2 (fun hf0 ↦ h0 (by simp [hf0]))) (hf _ (not_le.1 h))
  · exact m.le_degree (mem_support_iff.2 h0)

variable (m)

/-- The polynomial `∑_b q_b b` represented by `q`. -/
private abbrev lin {G : Set (_root_.MvPolynomial σ K)} (q : G →₀ _root_.MvPolynomial σ K) :
    _root_.MvPolynomial σ K :=
  Finsupp.linearCombination _ (fun b : G ↦ (b : _root_.MvPolynomial σ K)) q

/-- The summands of `q` that reach the bound `δ`. -/
private def top {G : Set (_root_.MvPolynomial σ K)} (δ : σ →₀ ℕ)
    (q : G →₀ _root_.MvPolynomial σ K) : Finset G := by
  classical
  exact q.support.filter fun b ↦ ((b : _root_.MvPolynomial σ K) * q b).coeff δ ≠ 0

private theorem mem_top {G : Set (_root_.MvPolynomial σ K)} {δ : σ →₀ ℕ}
    {q : G →₀ _root_.MvPolynomial σ K} {b : G} :
    b ∈ top δ q ↔ ((b : _root_.MvPolynomial σ K) * q b).coeff δ ≠ 0 := by
  classical
  simp only [top, Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
  intro h hq
  exact h (by simp [hq])

private theorem top_subset {G : Set (_root_.MvPolynomial σ K)} (δ : σ →₀ ℕ)
    (q : G →₀ _root_.MvPolynomial σ K) : top δ q ⊆ q.support := by
  intro b hb
  simp only [top, Finset.mem_filter] at hb
  exact hb.1

private theorem coeff_lin {G : Set (_root_.MvPolynomial σ K)} (δ : σ →₀ ℕ)
    (q : G →₀ _root_.MvPolynomial σ K) :
    (lin q).coeff δ = ∑ b ∈ q.support, ((b : _root_.MvPolynomial σ K) * q b).coeff δ := by
  rw [lin, Finsupp.linearCombination_apply, Finsupp.sum, coeff_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [smul_eq_mul, mul_comm]

private theorem leDeg_lin {G : Set (_root_.MvPolynomial σ K)} {δ : σ →₀ ℕ}
    {q : G →₀ _root_.MvPolynomial σ K}
    (hq : ∀ b : G, LeDeg m δ ((b : _root_.MvPolynomial σ K) * q b)) : LeDeg m δ (lin q) := by
  intro d hd
  rw [coeff_lin]
  exact Finset.sum_eq_zero fun b _ ↦ hq b d hd

open Classical in
/-- The rewriting step: two summands reaching `δ` let one move its top term onto the other. -/
private theorem step {G : Set (_root_.MvPolynomial σ K)}
    (hG0 : (0 : _root_.MvPolynomial σ K) ∉ G)
    (hS : ∀ g ∈ G, ∀ h ∈ G, ∃ p : G →₀ _root_.MvPolynomial σ K,
      m.sPolynomial g h = lin p ∧
        ∀ b : G, m.degree ((b : _root_.MvPolynomial σ K) * p b) ≼[m]
          m.degree (m.sPolynomial g h))
    {δ : σ →₀ ℕ} {q : G →₀ _root_.MvPolynomial σ K}
    (hq : ∀ b : G, LeDeg m δ ((b : _root_.MvPolynomial σ K) * q b)) {i j : G}
    (hi : i ∈ top δ q) (hj : j ∈ top δ q) (hij : i ≠ j) :
    ∃ q' : G →₀ _root_.MvPolynomial σ K, lin q' = lin q ∧
      (∀ b : G, LeDeg m δ ((b : _root_.MvPolynomial σ K) * q' b)) ∧
      top δ q' ⊆ (top δ q).erase i := by
  classical
  set gi : _root_.MvPolynomial σ K := i.1
  set gj : _root_.MvPolynomial σ K := j.1
  have hgi : gi ≠ 0 := fun h ↦ hG0 (h ▸ i.2)
  have hgj : gj ≠ 0 := fun h ↦ hG0 (h ▸ j.2)
  have hi' := mem_top.1 hi
  have hj' := mem_top.1 hj
  have hqi : q i ≠ 0 := fun h ↦ hi' (by simp [h])
  have hqj : q j ≠ 0 := fun h ↦ hj' (by simp [h])
  -- the summands reaching `δ` have leading monomial `δ`
  have hdi : m.degree gi + m.degree (q i) = δ := by
    rw [← m.degree_mul hgi hqi]; exact degree_eq_of_leDeg (hq i) hi'
  have hdj : m.degree gj + m.degree (q j) = δ := by
    rw [← m.degree_mul hgj hqj]; exact degree_eq_of_leDeg (hq j) hj'
  set a := m.degree gi
  set bb := m.degree gj
  set α := m.degree (q i)
  set c := m.leadingCoeff (q i)
  set γ := a ⊔ bb
  have haγ : a ≤ γ := le_sup_left
  have hbγ : bb ≤ γ := le_sup_right
  have hγδ : γ ≤ δ := sup_le (hdi ▸ le_self_add) (hdj ▸ le_self_add)
  have hlci : m.leadingCoeff gi ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hgi
  have hlcj : m.leadingCoeff gj ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hgj
  -- a standard representation of `S(gi, gj)` strictly below `γ`
  obtain ⟨p, hp, hpdeg⟩ : ∃ p : G →₀ _root_.MvPolynomial σ K,
      m.sPolynomial gi gj = lin p ∧
        ∀ b : G, LtDeg m γ ((b : _root_.MvPolynomial σ K) * p b) := by
    by_cases hS0 : m.sPolynomial gi gj = 0
    · exact ⟨0, by simp [hS0], fun b ↦ by simpa using ltDeg_zero γ⟩
    · obtain ⟨p, hp, hpd⟩ := hS gi i.2 gj j.2
      have hlt : m.toSyn (m.degree (m.sPolynomial gi gj)) < m.toSyn γ :=
        m.degree_sPolynomial_lt_sup_degree hS0
      refine ⟨p, hp, fun b ↦ LtDeg.mono (fun d hd ↦ ?_) hlt⟩
      exact leDeg_degree _ d ((hpd b).trans_lt hd)
  set M : _root_.MvPolynomial σ K := monomial (δ - γ) (c / m.leadingCoeff gj)
  set Xj : _root_.MvPolynomial σ K := monomial (δ - bb) (c * m.leadingCoeff gi /
    m.leadingCoeff gj)
  set LT : _root_.MvPolynomial σ K := monomial α c
  -- the key identity `c x^α gi = Xj gj + M S(gi, gj)`
  have hkey : LT * gi = Xj * gj + M * m.sPolynomial gi gj := by
    have e1 : δ - γ + (γ - a) = α := by
      rw [tsub_add_tsub_cancel hγδ haγ, ← hdi, add_tsub_cancel_left]
    have e2 : δ - γ + (γ - bb) = δ - bb := tsub_add_tsub_cancel hγδ hbγ
    rw [m.sPolynomial_def]
    change LT * gi = Xj * gj + M * (monomial (γ - a) (m.leadingCoeff gj) * gi -
      monomial (γ - bb) (m.leadingCoeff gi) * gj)
    simp only [M, Xj, LT, mul_sub, ← mul_assoc, monomial_mul_monomial, e1, e2]
    rw [div_mul_cancel₀ c hlcj, show c / m.leadingCoeff gj * m.leadingCoeff gi =
      c * m.leadingCoeff gi / m.leadingCoeff gj by ring]
    ring
  refine ⟨q - Finsupp.single i LT + Finsupp.single j Xj + M • p, ?_, ?_, ?_⟩
  · simp only [lin, map_add, map_sub, map_smul, Finsupp.linearCombination_single, smul_eq_mul]
    change lin q - LT * gi + Xj * gj + M * lin p = lin q
    rw [← hp, hkey]; ring
  · intro b
    have hexp : (b : _root_.MvPolynomial σ K) *
        (q - Finsupp.single i LT + Finsupp.single j Xj + M • p) b =
        (b : _root_.MvPolynomial σ K) * q b - (b : _root_.MvPolynomial σ K) *
          Finsupp.single i LT b + (b : _root_.MvPolynomial σ K) * Finsupp.single j Xj b +
          M * ((b : _root_.MvPolynomial σ K) * p b) := by
      simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]; ring
    rw [hexp]
    refine (((hq b).sub ?_).add ?_).add ?_
    · by_cases hb : b = i
      · subst hb
        rw [Finsupp.single_eq_same, ← hdi]
        exact (leDeg_degree gi).mul (leDeg_monomial α c)
      · rw [Finsupp.single_eq_of_ne hb, mul_zero]; exact leDeg_zero δ
    · by_cases hb : b = j
      · subst hb
        rw [Finsupp.single_eq_same]
        have := (leDeg_degree (m := m) gj).mul (leDeg_monomial (δ - bb)
          (c * m.leadingCoeff gi / m.leadingCoeff gj))
        rwa [add_tsub_cancel_of_le (hdj ▸ le_self_add)] at this
      · rw [Finsupp.single_eq_of_ne hb, mul_zero]; exact leDeg_zero δ
    · have := LtDeg.mul (leDeg_monomial (m := m) (δ - γ) (c / m.leadingCoeff gj)) (hpdeg b)
      rw [tsub_add_cancel_of_le hγδ] at this
      exact this.leDeg
  · intro b hb
    rw [mem_top] at hb
    have hMp : (M * ((b : _root_.MvPolynomial σ K) * p b)).coeff δ = 0 := by
      have := LtDeg.mul (leDeg_monomial (m := m) (δ - γ) (c / m.leadingCoeff gj)) (hpdeg b)
      rw [tsub_add_cancel_of_le hγδ] at this
      exact this δ le_rfl
    have hexp : ((b : _root_.MvPolynomial σ K) *
        (q - Finsupp.single i LT + Finsupp.single j Xj + M • p) b).coeff δ =
        ((b : _root_.MvPolynomial σ K) * (q b - Finsupp.single i LT b)).coeff δ +
          ((b : _root_.MvPolynomial σ K) * Finsupp.single j Xj b).coeff δ := by
      have e : (b : _root_.MvPolynomial σ K) *
          (q - Finsupp.single i LT + Finsupp.single j Xj + M • p) b =
          (b : _root_.MvPolynomial σ K) * (q b - Finsupp.single i LT b) +
            (b : _root_.MvPolynomial σ K) * Finsupp.single j Xj b +
            M * ((b : _root_.MvPolynomial σ K) * p b) := by
        simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]; ring
      rw [e, coeff_add, hMp, add_zero, coeff_add]
    rw [hexp] at hb
    have hbi : b ≠ i := by
      rintro rfl
      apply hb
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, mul_zero, coeff_zero', add_zero]
      have := LtDeg.mul (leDeg_degree (m := m) gi) (ltDeg_sub_leadingTerm (m := m) (q b))
      rw [hdi] at this
      exact this δ le_rfl
    refine Finset.mem_erase.2 ⟨hbi, ?_⟩
    by_cases hbj : b = j
    · exact hbj ▸ hj
    · rw [Finsupp.single_eq_of_ne hbi, Finsupp.single_eq_of_ne hbj,
        sub_zero, mul_zero, coeff_zero', add_zero] at hb
      exact mem_top.2 hb

/-- The bound `δ` given by the largest leading monomial of the summands. -/
private theorem exists_bound {G : Set (_root_.MvPolynomial σ K)}
    (q : G →₀ _root_.MvPolynomial σ K)
    (hne : q.support.Nonempty) :
    ∃ δ' : σ →₀ ℕ, (∀ b : G, LeDeg m δ' ((b : _root_.MvPolynomial σ K) * q b)) ∧
      ∃ b ∈ q.support, m.degree ((b : _root_.MvPolynomial σ K) * q b) = δ' := by
  obtain ⟨b₀, hb₀, hmax⟩ := q.support.exists_max_image
    (fun b ↦ m.toSyn (m.degree ((b : _root_.MvPolynomial σ K) * q b))) hne
  refine ⟨_, fun b ↦ ?_, b₀, hb₀, rfl⟩
  by_cases hb : b ∈ q.support
  · intro d hd
    exact leDeg_degree _ d ((hmax b hb).trans_lt hd)
  · rw [Finsupp.notMem_support_iff.1 hb, mul_zero]; exact leDeg_zero _

private theorem main {G : Set (_root_.MvPolynomial σ K)}
    (hG0 : (0 : _root_.MvPolynomial σ K) ∉ G)
    (hS : ∀ g ∈ G, ∀ h ∈ G, ∃ p : G →₀ _root_.MvPolynomial σ K,
      m.sPolynomial g h = lin p ∧
        ∀ b : G, m.degree ((b : _root_.MvPolynomial σ K) * p b) ≼[m]
          m.degree (m.sPolynomial g h)) :
    ∀ (s : m.syn) (n : ℕ) (q : G →₀ _root_.MvPolynomial σ K),
      (∀ b : G, LeDeg m (m.toSyn.symm s) ((b : _root_.MvPolynomial σ K) * q b)) →
      (top (m.toSyn.symm s) q).card ≤ n → lin q ≠ 0 →
      ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree (lin q) := by
  classical
  intro s
  induction s using WellFoundedLT.induction with
  | _ s ihs =>
  -- no summand reaches the bound: lower it to the largest leading monomial
  have drop : ∀ q : G →₀ _root_.MvPolynomial σ K,
      (∀ b : G, LeDeg m (m.toSyn.symm s) ((b : _root_.MvPolynomial σ K) * q b)) →
      top (m.toSyn.symm s) q = ∅ → lin q ≠ 0 →
      ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree (lin q) := by
    intro q hq htop hf
    set δ := m.toSyn.symm s
    have hlow : ∀ b : G, LtDeg m δ ((b : _root_.MvPolynomial σ K) * q b) := fun b ↦
      ltDeg_of_leDeg_of_coeff (hq b) (by
        by_contra h
        have := mem_top.2 h
        rw [htop] at this
        exact Finset.notMem_empty _ this)
    have hne : q.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]; rintro rfl; exact hf (by simp [lin])
    obtain ⟨δ', hδ', b, hb, hbδ⟩ := exists_bound m q hne
    have hbne : (b : _root_.MvPolynomial σ K) * q b ≠ 0 :=
      mul_ne_zero (fun h ↦ hG0 (h ▸ b.2)) (Finsupp.mem_support_iff.1 hb)
    have hlt : m.toSyn δ' < s := by
      by_contra hle
      have h1 : m.toSyn δ ≤ m.toSyn (m.degree ((b : _root_.MvPolynomial σ K) * q b)) := by
        simpa [δ, hbδ] using not_lt.1 hle
      exact (m.coeff_degree_ne_zero_iff.2 hbne) (hlow b _ h1)
    exact ihs _ hlt _ q (by simpa using hδ') le_rfl hf
  intro n
  induction n with
  | zero =>
    intro q hq hcard hf
    exact drop q hq (Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)) hf
  | succ n ihn =>
    intro q hq hcard hf
    set δ := m.toSyn.symm s
    by_cases hcoeff : (lin q).coeff δ = 0
    · by_cases hT : top δ q = ∅
      · exact drop q hq hT hf
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hT
        -- a second summand reaching `δ`, since the top coefficients cancel
        have hsum : ∑ b ∈ top δ q, ((b : _root_.MvPolynomial σ K) * q b).coeff δ = 0 := by
          rw [← hcoeff, coeff_lin]
          refine (Finset.sum_subset (f := fun b : G ↦ ((b : _root_.MvPolynomial σ K) * q b).coeff δ)
            (top_subset δ q) fun b _ hb ↦ ?_)
          by_contra h
          exact hb (mem_top.2 h)
        rw [← Finset.add_sum_erase _ _ hi] at hsum
        have hrest : ∑ b ∈ (top δ q).erase i,
            ((b : _root_.MvPolynomial σ K) * q b).coeff δ ≠ 0 := by
          intro h
          rw [h, add_zero] at hsum
          exact mem_top.1 hi hsum
        obtain ⟨j, hj, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrest
        obtain ⟨q', hlin, hq', hsub⟩ := step m hG0 hS hq hi (Finset.mem_of_mem_erase hj)
          (Ne.symm (Finset.ne_of_mem_erase hj))
        have hc : (top δ q').card ≤ n := by
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hi] at this
          omega
        rw [← hlin] at hf ⊢
        exact ihn q' hq' hc hf
    · -- the coefficient of `x^δ` survives: `δ` is the leading monomial of `f`
      have hdeg : m.degree (lin q) = δ := degree_eq_of_leDeg (leDeg_lin m hq) hcoeff
      rw [coeff_lin] at hcoeff
      obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
      have hqb : q b ≠ 0 := fun h ↦ hb (by simp [h])
      have hb0 : (b : _root_.MvPolynomial σ K) ≠ 0 := fun h ↦ hG0 (h ▸ b.2)
      refine ⟨b, b.2, hb0, ?_⟩
      rw [hdeg, ← degree_eq_of_leDeg (hq b) hb, m.degree_mul hb0 hqb]
      exact le_self_add

/-- **Buchberger's criterion** (Cox–Little–O'Shea, *Ideals, Varieties, and Algorithms*,
Ch. 2 §6, Theorem 6; B. Hassett, *Math 465 Lecture Notes*, Brown University, 2002, Lecture 5,
Theorem 5.2). Let `m` be a monomial order and `G` a set of nonzero polynomials over a field.
If for all `g, h ∈ G` the S-polynomial `S(g, h)` can be written as `∑_{b ∈ G} q_b b` with
`m.degree (b q_b) ≼ m.degree S(g, h)` for every `b`, then `G` is a Gröbner basis of the ideal
it generates. Such a representation is what a division of `S(g, h)` by `G` with zero remainder
provides, and it is the form in which Hassett's proof of Theorem 5.2 uses the hypothesis. -/
theorem isGroebnerBasis_of_sPolynomial (G : Set (_root_.MvPolynomial σ K))
    (hG0 : (0 : _root_.MvPolynomial σ K) ∉ G)
    (hS : ∀ g ∈ G, ∀ h ∈ G, ∃ q : G →₀ _root_.MvPolynomial σ K,
      m.sPolynomial g h =
          Finsupp.linearCombination _ (fun b : G ↦ (b : _root_.MvPolynomial σ K)) q ∧
        ∀ b : G, m.degree ((b : _root_.MvPolynomial σ K) * q b) ≼[m]
          m.degree (m.sPolynomial g h)) :
    IsGroebnerBasis m G (Ideal.span G) := by
  refine ⟨Ideal.subset_span, fun f hf hf0 ↦ ?_⟩
  obtain ⟨q, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).1 hf
  have hne : q.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]; rintro rfl; exact hf0 (by simp)
  obtain ⟨δ', hδ', -⟩ := exists_bound m q hne
  exact main m hG0 hS (m.toSyn δ') _ q (by simpa using hδ') le_rfl hf0

end MathlibExt.RingTheory.MvPolynomial.BuchbergerCriterion
