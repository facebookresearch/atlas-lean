/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvexDistance
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Talagrand's convex-distance inequality on a product of finite sets

For a finite set `Ω` with probability weights `p` and the product weights
`P(x) = ∏_i p(x_i)` on `Ω^N`, Talagrand's Theorem 4.1.1 states
`∑_x P(x) exp(f_c(A, x)² / 4) ≤ 1 / P(A)` for every `A ⊆ Ω^N`. It is proved here, in the form
`(∑_x P(x) exp(f_c(A, x)² / 4)) · P(A) ≤ 1` (which also covers `P(A) = 0`), by Talagrand's
induction on `N`:

* splitting `z ∈ Ω^{N+1}` as `(ω, x)` with `ω` the first coordinate, the section
  `A(ω) = {x : (ω, x) ∈ A}` and the projection `B = {x : ∃ ω', (ω', x) ∈ A}` satisfy
  `f_c(A, (ω, x))² ≤ (1 - λ)² + λ f_c(A(ω), x)² + (1 - λ) f_c(B, x)²` for `0 ≤ λ ≤ 1` (the source's
  (4.1.7));
* Hölder's inequality and the induction hypothesis bound the `x`-sum by
  `e^{(1-λ)²/4} P(A(ω))^{-λ} P(B)^{-(1-λ)}`;
* the numerical Lemma 4.1.3, `inf_λ r^{-λ} e^{(1-λ)²/4} ≤ 2 - r` for `0 ≤ r ≤ 1`, and
  `u (2 - u) ≤ 1` conclude.

The numerical lemma is proved with Taylor bounds for the exponential instead of the source's
study of a derivative. The statement for a general probability space `(Ω, μ)` is recorded in
`MathlibExt.Probability.ConvexDistanceWanted`.

## References

* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205, Theorem 4.1.1, Lemma 4.1.3 and their proofs.
-/

@[expose] public section

namespace MathlibExt.Probability.ConvexDistance

open Metric Real Finset

/-! ### The numerical lemma -/

/-- **Talagrand's numerical lemma** (Talagrand, *Concentration of measure and isoperimetric
inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Lemma 4.1.3, taken there from
Johnson and Schechtman). For `0 ≤ r ≤ 1` there is `λ ∈ [0, 1]` with
`r^{-λ} exp((1 - λ)² / 4) ≤ 2 - r`; here in the form `exp((1 - λ)² / 4) ≤ (2 - r) r^λ`, with
`λ = 0` unless `r > 0`. -/
theorem exists_exp_le_two_sub_mul_rpow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ (l = 0 ∨ 0 < r) ∧ exp ((1 - l) ^ 2 / 4) ≤ (2 - r) * r ^ l := by
  by_cases h : exp (-1 / 2) ≤ r
  · have hr : 0 < r := lt_of_lt_of_le (exp_pos _) h
    set L := log r with hLdef
    have hL0 : L ≤ 0 := log_nonpos hr0 hr1
    have hL1 : -1 / 2 ≤ L := by
      rw [hLdef, ← log_exp (-1 / 2)]; exact log_le_log (exp_pos _) h
    refine ⟨1 + 2 * L, by linarith, by linarith, Or.inr hr, ?_⟩
    have hrL : r = exp L := (exp_log hr).symm
    rw [rpow_def_of_pos hr, ← hLdef]
    -- reduce to `exp (-L²) ≤ 1 - (1 - e^L)²`
    have hkey : exp (-L ^ 2) ≤ 1 - (1 - exp L) ^ 2 := by
      have hL : |L| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h1 := Real.exp_bound hL (n := 4) (by norm_num)
      have h2 := Real.exp_bound (x := -L ^ 2) (by rw [abs_neg, abs_pow]; nlinarith [abs_nonneg L])
        (n := 3) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
      norm_num at h1 h2
      rw [abs_le] at h1 h2
      have hy1 : exp L ≤ 1 := exp_le_one_iff.mpr hL0
      set a := -L with ha
      have ha0 : 0 ≤ a := by linarith
      have ha1 : a ≤ 1 / 2 := by linarith
      have hLa : L = -a := by linarith
      rw [hLa] at h1 h2 hy1 ⊢
      set y := exp (-a)
      have hlow : 1 - a + a ^ 2 / 2 - a ^ 3 / 6 - 5 / 96 * a ^ 4 ≤ y := by
        have h := h1.1
        rw [abs_neg, abs_of_nonneg ha0] at h
        ring_nf at h ⊢; linarith
      have hexp : exp (-(-a) ^ 2) ≤ 1 - a ^ 2 + a ^ 4 / 2 + 2 / 9 * a ^ 6 := by
        have h := h2.2
        ring_nf at h ⊢; linarith
      have hc : 0 ≤ 1 - y := by linarith
      have hc2 : 1 - y ≤ a - a ^ 2 / 2 + a ^ 3 / 6 + 5 / 96 * a ^ 4 := by linarith
      have hsq : (1 - y) ^ 2 ≤ (a - a ^ 2 / 2 + a ^ 3 / 6 + 5 / 96 * a ^ 4) ^ 2 :=
        pow_le_pow_left₀ hc hc2 2
      have hQ : 0 ≤ 1 - 13 / 12 * a + 1 / 16 * a ^ 2 - 19 / 96 * a ^ 3 - 5 / 288 * a ^ 4 -
          25 / 9216 * a ^ 5 := by
        have h3 : a ^ 3 ≤ 1 / 8 := by
          calc a ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ ha0 ha1 3
            _ = 1 / 8 := by norm_num
        have h4 : a ^ 4 ≤ 1 / 16 := by
          calc a ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ ha0 ha1 4
            _ = 1 / 16 := by norm_num
        have h5 : a ^ 5 ≤ 1 / 32 := by
          calc a ^ 5 ≤ (1 / 2) ^ 5 := pow_le_pow_left₀ ha0 ha1 5
            _ = 1 / 32 := by norm_num
        nlinarith [sq_nonneg a]
      have hD : 0 ≤ a ^ 3 * (1 - 13 / 12 * a + 1 / 16 * a ^ 2 - 19 / 96 * a ^ 3 -
          5 / 288 * a ^ 4 - 25 / 9216 * a ^ 5) := mul_nonneg (pow_nonneg ha0 3) hQ
      nlinarith [hexp, hsq, hD]
    have hfin : exp ((1 - (1 + 2 * L)) ^ 2 / 4) = exp (L ^ 2) := by congr 1; ring
    rw [hfin]
    have hpos : 0 < exp (L * (1 + 2 * L)) := exp_pos _
    calc exp (L ^ 2) = exp (-L ^ 2) * exp (L * (1 + 2 * L)) * exp (-L) := by
          rw [← exp_add, ← exp_add]; congr 1; ring
      _ ≤ (1 - (1 - exp L) ^ 2) * exp (L * (1 + 2 * L)) * exp (-L) := by gcongr
      _ = (2 - exp L) * exp (L * (1 + 2 * L)) := by
          have : exp L * exp (-L) = 1 := by rw [← exp_add]; simp
          have hrw : (1 - (1 - exp L) ^ 2) = exp L * (2 - exp L) := by ring
          rw [hrw]
          calc exp L * (2 - exp L) * exp (L * (1 + 2 * L)) * exp (-L)
              = (exp L * exp (-L)) * ((2 - exp L) * exp (L * (1 + 2 * L))) := by ring
            _ = _ := by rw [this, one_mul]
      _ = (2 - r) * exp (L * (1 + 2 * L)) := by rw [hrL]
  · push Not at h
    refine ⟨0, le_rfl, zero_le_one, Or.inl rfl, ?_⟩
    rw [rpow_zero, mul_one, sub_zero, one_pow]
    have he1 : exp (1 / 4) ≤ 1.29 := by
      have := Real.exp_bound' (x := 1 / 4) (by norm_num) (by norm_num) (n := 3) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this
      linarith
    have he2 : exp (-1 / 2) ≤ 0.62 := by
      have hq := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, exp_neg]
      rw [inv_le_comm₀ (exp_pos _) (by norm_num)]
      norm_num at hq ⊢
      linarith
    linarith

/-! ### Weighted Hölder inequality -/

/-- **Weighted Hölder inequality for two factors.** For nonnegative weights and values and
`0 ≤ λ ≤ 1`, `∑ w a^λ b^{1-λ} ≤ (∑ w a)^λ (∑ w b)^{1-λ}`. -/
theorem sum_mul_rpow_mul_rpow_le {ι : Type*} (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    ∑ i ∈ s, w i * (a i ^ l * b i ^ (1 - l)) ≤
      (∑ i ∈ s, w i * a i) ^ l * (∑ i ∈ s, w i * b i) ^ (1 - l) := by
  rcases hl0.lt_or_eq with hl0' | rfl
  · rcases hl1.lt_or_eq with hl1' | rfl
    · have hpq := Real.HolderConjugate.inv_one_sub_inv hl0' hl1'
      have hf : ∀ i ∈ s, 0 ≤ (w i * a i) ^ l := fun i _ => rpow_nonneg (mul_nonneg (hw i) (ha i)) _
      have hg : ∀ i ∈ s, 0 ≤ (w i * b i) ^ (1 - l) :=
        fun i _ => rpow_nonneg (mul_nonneg (hw i) (hb i)) _
      have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s) (f := fun i => (w i * a i) ^ l)
        (g := fun i => (w i * b i) ^ (1 - l)) hpq hf hg
      have hl' : l ≠ 0 := hl0'.ne'
      have hl'' : 1 - l ≠ 0 := (sub_pos.mpr hl1').ne'
      have e1 : ∀ i, ((w i * a i) ^ l) ^ l⁻¹ = w i * a i := fun i =>
        rpow_rpow_inv (mul_nonneg (hw i) (ha i)) hl'
      have e2 : ∀ i, ((w i * b i) ^ (1 - l)) ^ (1 - l)⁻¹ = w i * b i := fun i =>
        rpow_rpow_inv (mul_nonneg (hw i) (hb i)) hl''
      simp only [e1, e2, one_div, inv_inv] at h
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_rpow (hw i) (ha i), mul_rpow (hw i) (hb i)]
      have : w i ^ l * w i ^ (1 - l) = w i := by
        rw [← rpow_add' (hw i) (by simp), add_sub_cancel, rpow_one]
      calc w i * (a i ^ l * b i ^ (1 - l))
          = (w i ^ l * w i ^ (1 - l)) * (a i ^ l * b i ^ (1 - l)) := by rw [this]
        _ = _ := by ring
    · simp
  · simp

/-! ### The geometric step -/

variable {Ω : Type*} {N : ℕ}

-- The vector `(c, s) ∈ ℝ^{N+1}` for `c ∈ ℝ` and `s ∈ ℝ^N`.
private noncomputable def consVec (c : ℝ) (s : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin (N + 1)) :=
  WithLp.toLp 2 (Fin.cons c (WithLp.ofLp s) : Fin (N + 1) → ℝ)

@[simp] private theorem consVec_zero_apply (c : ℝ) (s : EuclideanSpace ℝ (Fin N)) :
    consVec c s 0 = c := rfl

@[simp] private theorem consVec_succ_apply (c : ℝ) (s : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    consVec c s i.succ = s i := rfl

private theorem norm_consVec_sq (c : ℝ) (s : EuclideanSpace ℝ (Fin N)) :
    ‖consVec c s‖ ^ 2 = c ^ 2 + ‖s‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, sq_sqrt (by positivity),
    sq_sqrt (by positivity), Fin.sum_univ_succ]
  simp

-- `s ↦ (0, s)` as a linear map.
private noncomputable def consZeroL :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin (N + 1)) where
  toFun s := consVec 0 s
  map_add' s t := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c s := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

-- `s ↦ (1, s)` as an affine map.
private noncomputable def consOneA :
    EuclideanSpace ℝ (Fin N) →ᵃ[ℝ] EuclideanSpace ℝ (Fin (N + 1)) where
  toFun s := consVec 1 s
  linear := consZeroL
  map_vadd' p v := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZeroL]

private theorem consVec_combo (l : ℝ) (s t : EuclideanSpace ℝ (Fin N)) :
    l • consVec 0 s + (1 - l) • consVec 1 t = consVec (1 - l) (l • s + (1 - l) • t) := by
  ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **Section at the first coordinate.** The section `A(ω) = {x : (ω, x) ∈ A}` of
`A ⊆ Ω^{N+1}` at the first coordinate `ω`. -/
def sectionAt (A : Set (Fin (N + 1) → Ω)) (ω : Ω) : Set (Fin N → Ω) := {x | Fin.cons ω x ∈ A}

/-- **Projection forgetting the first coordinate.** The projection
`B = {x : ∃ ω, (ω, x) ∈ A}` of `A ⊆ Ω^{N+1}`. -/
def projection (A : Set (Fin (N + 1) → Ω)) : Set (Fin N → Ω) := {x | ∃ ω, Fin.cons ω x ∈ A}

theorem sectionAt_subset_projection (A : Set (Fin (N + 1) → Ω)) (ω : Ω) :
    sectionAt A ω ⊆ projection A := fun _ hx => ⟨ω, hx⟩

private theorem consVec_zero_mem_convexSupport {A : Set (Fin (N + 1) → Ω)} {ω : Ω} {x : Fin N → Ω}
    {s : EuclideanSpace ℝ (Fin N)} (hs : s ∈ convexSupport (sectionAt A ω) x) :
    consVec 0 s ∈ convexSupport A (Fin.cons ω x) := by
  obtain ⟨y, hy, h01, hag⟩ := hs
  refine ⟨Fin.cons ω y, hy, fun i => ?_, fun i hi => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using h01 j
  · induction i using Fin.cases with
    | zero => simp
    | succ j => simpa using hag j (by simpa using hi)

private theorem consVec_one_mem_convexSupport {A : Set (Fin (N + 1) → Ω)} {ω : Ω} {x : Fin N → Ω}
    {t : EuclideanSpace ℝ (Fin N)} (ht : t ∈ convexSupport (projection A) x) :
    consVec 1 t ∈ convexSupport A (Fin.cons ω x) := by
  obtain ⟨y, ⟨ω', hy⟩, h01, hag⟩ := ht
  refine ⟨Fin.cons ω' y, hy, fun i => ?_, fun i hi => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using h01 j
  · induction i using Fin.cases with
    | zero => simp at hi
    | succ j => simpa using hag j (by simpa using hi)

theorem convexSupport_finite (A : Set (Fin N → Ω)) (x : Fin N → Ω) :
    (convexSupport A x).Finite := by
  classical
  refine (Set.finite_range fun b : Fin N → Bool =>
    (WithLp.toLp 2 fun i => if b i then (1 : ℝ) else 0 : EuclideanSpace ℝ (Fin N))).subset ?_
  rintro s ⟨y, -, h01, -⟩
  refine ⟨fun i => decide (s i = 1), ?_⟩
  ext i
  rcases h01 i with h | h <;> simp [h]

theorem convexSupport_nonempty {A : Set (Fin N → Ω)} (hA : A.Nonempty) (x : Fin N → Ω) :
    (convexSupport A x).Nonempty := by
  classical
  obtain ⟨y, hy⟩ := hA
  refine ⟨WithLp.toLp 2 fun i => if x i ≠ y i then 1 else 0, y, hy, fun i => ?_, fun i hi => ?_⟩
  · by_cases h : x i ≠ y i <;> simp [h]
  · by_cases h : x i ≠ y i
    · simp [h] at hi
    · exact (not_not.mp h).symm

theorem exists_mem_convexHull_norm_eq {A : Set (Fin N → Ω)} (hA : A.Nonempty) (x : Fin N → Ω) :
    ∃ s ∈ convexHull ℝ (convexSupport A x), ‖s‖ = convexDistance A x := by
  obtain ⟨s, hs, hd⟩ :=
    (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (convexSupport_finite A x)).exists_infDist_eq_dist
    ((convexSupport_nonempty hA x).mono (subset_convexHull ℝ _)) 0
  exact ⟨s, hs, by rw [convexDistance, hd, dist_zero_left]⟩

/-- **Talagrand's geometric step** (Talagrand, *Concentration of measure and isoperimetric
inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), proof of Theorem 4.1.1, (4.1.7)).
For `A ⊆ Ω^{N+1}`, `ω ∈ Ω`, `x ∈ Ω^N` and `0 ≤ λ ≤ 1`,
`f_c(A, (ω, x))² ≤ (1 - λ)² + λ f_c(A(ω), x)² + (1 - λ) f_c(B, x)²`, where `A(ω)` is the
section and `B` the projection; the projection must be nonempty, and so must the section unless
`λ = 0`. -/
theorem convexDistance_cons_sq_le (A : Set (Fin (N + 1) → Ω)) (ω : Ω) (x : Fin N → Ω) {l : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hB : (projection A).Nonempty)
    (hsec : l = 0 ∨ (sectionAt A ω).Nonempty) :
    convexDistance A (Fin.cons ω x) ^ 2 ≤
      (1 - l) ^ 2 + l * convexDistance (sectionAt A ω) x ^ 2 +
        (1 - l) * convexDistance (projection A) x ^ 2 := by
  obtain ⟨t, ht, htn⟩ := exists_mem_convexHull_norm_eq hB x
  have ht' : consVec 1 t ∈ convexHull ℝ (convexSupport A (Fin.cons ω x)) := by
    have h : consOneA t ∈ consOneA '' convexHull ℝ (convexSupport (projection A) x) :=
      ⟨t, ht, rfl⟩
    rw [AffineMap.image_convexHull] at h
    exact convexHull_mono (by rintro _ ⟨u, hu, rfl⟩; exact consVec_one_mem_convexSupport hu) h
  have hfc0 := convexDistance_nonneg A (Fin.cons ω x)
  rcases hsec with rfl | hne
  · have hle : convexDistance A (Fin.cons ω x) ≤ ‖consVec 1 t‖ := by
      rw [← dist_zero_left]; exact infDist_le_dist_of_mem ht'
    have := pow_le_pow_left₀ hfc0 hle 2
    rw [norm_consVec_sq, htn] at this
    simpa using this
  · obtain ⟨s, hs, hsn⟩ := exists_mem_convexHull_norm_eq hne x
    have hs' : consVec 0 s ∈ convexHull ℝ (convexSupport A (Fin.cons ω x)) := by
      have h : consZeroL s ∈ consZeroL '' convexHull ℝ (convexSupport (sectionAt A ω) x) :=
        ⟨s, hs, rfl⟩
      rw [LinearMap.image_convexHull] at h
      exact convexHull_mono (by rintro _ ⟨u, hu, rfl⟩; exact consVec_zero_mem_convexSupport hu) h
    have hp : consVec (1 - l) (l • s + (1 - l) • t) ∈
        convexHull ℝ (convexSupport A (Fin.cons ω x)) := by
      rw [← consVec_combo]
      exact convex_convexHull ℝ _ hs' ht' hl0 (by linarith) (by ring)
    have hle : convexDistance A (Fin.cons ω x) ≤ ‖consVec (1 - l) (l • s + (1 - l) • t)‖ := by
      rw [← dist_zero_left]; exact infDist_le_dist_of_mem hp
    have h2 := pow_le_pow_left₀ hfc0 hle 2
    rw [norm_consVec_sq] at h2
    have hconv : ‖l • s + (1 - l) • t‖ ^ 2 ≤ l * ‖s‖ ^ 2 + (1 - l) * ‖t‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        Real.norm_of_nonneg hl0, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - l)]
      have hst : 2 * inner ℝ s t ≤ ‖s‖ ^ 2 + ‖t‖ ^ 2 := by
        nlinarith [norm_sub_sq_real s t, sq_nonneg ‖s - t‖]
      have hl : 0 ≤ l * (1 - l) := mul_nonneg hl0 (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hst hl]
    rw [← hsn, ← htn]
    linarith

/-! ### Product weights on a finite set -/

/-- **Product weights.** For weights `p` on a finite set `Ω`, `P(x) = ∏_i p(x_i)` on `Ω^N`; when
`p` is a probability vector, `P` is the product probability `p^{⊗N}`. -/
def prodWeight (p : Ω → ℝ) (x : Fin N → Ω) : ℝ := ∏ i, p (x i)

theorem prodWeight_nonneg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (x : Fin N → Ω) :
    0 ≤ prodWeight p x :=
  Finset.prod_nonneg fun _ _ => hp _

theorem prodWeight_cons (p : Ω → ℝ) (ω : Ω) (x : Fin N → Ω) :
    prodWeight p (Fin.cons ω x : Fin (N + 1) → Ω) = p ω * prodWeight p x := by
  simp [prodWeight, Fin.prod_univ_succ]

variable [Fintype Ω]

/-- **Weight of a set.** `P(A) = ∑_{x ∈ A} P(x)` for `A ⊆ Ω^N`. -/
noncomputable def weightOf (p : Ω → ℝ) (A : Set (Fin N → Ω)) : ℝ :=
  ∑ x, A.indicator (prodWeight p) x

theorem sum_fin_succ_pi (F : (Fin (N + 1) → Ω) → ℝ) :
    ∑ z, F z = ∑ ω, ∑ x : Fin N → Ω, F (Fin.cons ω x) := by
  rw [← (Fin.consEquiv fun _ : Fin (N + 1) => Ω).sum_comp, Fintype.sum_prod_type]
  rfl

theorem weightOf_nonneg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (A : Set (Fin N → Ω)) :
    0 ≤ weightOf p A :=
  Finset.sum_nonneg fun x _ => by
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx, prodWeight_nonneg hp x]

theorem weightOf_mono {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {A B : Set (Fin N → Ω)} (h : A ⊆ B) :
    weightOf p A ≤ weightOf p B :=
  Finset.sum_le_sum fun x _ => by
    by_cases hx : x ∈ A
    · simp [Set.indicator, hx, h hx]
    · by_cases hxB : x ∈ B <;> simp [Set.indicator, hx, hxB, prodWeight_nonneg hp x]

theorem weightOf_cons (p : Ω → ℝ) (A : Set (Fin (N + 1) → Ω)) :
    weightOf p A = ∑ ω, p ω * weightOf p (sectionAt A ω) := by
  rw [weightOf, sum_fin_succ_pi]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [weightOf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : (Fin.cons ω x : Fin (N + 1) → Ω) ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ sectionAt A ω from hx),
      prodWeight_cons]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ sectionAt A ω from hx),
      mul_zero]

theorem nonempty_of_weightOf_pos {p : Ω → ℝ} {A : Set (Fin N → Ω)} (h : 0 < weightOf p A) :
    A.Nonempty := by
  by_contra hA
  rw [Set.not_nonempty_iff_eq_empty] at hA
  simp [weightOf, hA] at h

/-- **Talagrand's convex-distance inequality on a product of finite sets** (Talagrand,
*Concentration of measure and isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81
(1995), Theorem 4.1.1, (4.1.2), for a finite `Ω`). Let `p` be a probability vector on a finite
set `Ω` and `P = p^{⊗N}`. For every `N` and every `A ⊆ Ω^N`,
`(∑_x P(x) exp(f_c(A, x)² / 4)) · P(A) ≤ 1`, that is `∫ exp(f_c(A, ·)² / 4) dP ≤ 1 / P(A)`
when `P(A) > 0`. -/
theorem sum_exp_convexDistance_mul_weightOf_le (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) (N : ℕ) (A : Set (Fin N → Ω)) :
    (∑ x, prodWeight p x * exp (convexDistance A x ^ 2 / 4)) * weightOf p A ≤ 1 := by
  induction N with
  | zero =>
    by_cases hA : A.Nonempty
    · have hA' : ∀ x : Fin 0 → Ω, x ∈ A := fun x => by
        obtain ⟨y, hy⟩ := hA
        rwa [Subsingleton.elim x y]
      simp [weightOf, prodWeight, Set.indicator_of_mem (hA' _),
        convexDistance_eq_zero_of_mem (hA' _)]
    · rw [Set.not_nonempty_iff_eq_empty] at hA
      simp [weightOf, hA]
  | succ N ih =>
    set B := projection A
    set β := weightOf p B
    set α : Ω → ℝ := fun ω => weightOf p (sectionAt A ω) with hαdef
    have hα0 : ∀ ω, 0 ≤ α ω := fun ω => weightOf_nonneg hp0 _
    have hαβ : ∀ ω, α ω ≤ β := fun ω => weightOf_mono hp0 (sectionAt_subset_projection A ω)
    have hPA : weightOf p A = ∑ ω, p ω * α ω := weightOf_cons p A
    have hPA0 : 0 ≤ weightOf p A := weightOf_nonneg hp0 A
    rcases (weightOf_nonneg hp0 B).lt_or_eq with hβ | hβ
    swap
    · have hzero : weightOf p A = 0 := by
        rw [hPA]
        refine Finset.sum_eq_zero fun ω _ => ?_
        have : α ω = 0 := le_antisymm (hβ ▸ hαβ ω) (hα0 ω)
        rw [this, mul_zero]
      rw [hzero, mul_zero]
      exact zero_le_one
    have hBne : B.Nonempty := nonempty_of_weightOf_pos hβ
    have hω : ∀ ω, ∑ x : Fin N → Ω, prodWeight p x *
        exp (convexDistance A (Fin.cons ω x) ^ 2 / 4) ≤ (2 - α ω / β) / β := by
      intro ω
      set r := α ω / β with hrdef
      have hr0 : 0 ≤ r := div_nonneg (hα0 ω) hβ.le
      have hr1 : r ≤ 1 := (div_le_one hβ).mpr (hαβ ω)
      obtain ⟨l, hl0, hl1, hlr, hexp⟩ := exists_exp_le_two_sub_mul_rpow hr0 hr1
      have hαpos : 0 < r → 0 < α ω := fun hr => (div_pos_iff_of_pos_right hβ).mp hr
      have hsec : l = 0 ∨ (sectionAt A ω).Nonempty :=
        hlr.imp id fun hr => nonempty_of_weightOf_pos (hαpos hr)
      set J1 : (Fin N → Ω) → ℝ := fun x => exp (convexDistance (sectionAt A ω) x ^ 2 / 4)
      set J2 : (Fin N → Ω) → ℝ := fun x => exp (convexDistance B x ^ 2 / 4)
      have hpt : ∀ x, exp (convexDistance A (Fin.cons ω x) ^ 2 / 4) ≤
          exp ((1 - l) ^ 2 / 4) * (J1 x ^ l * J2 x ^ (1 - l)) := by
        intro x
        have hg := convexDistance_cons_sq_le A ω x hl0 hl1 hBne hsec
        simp only [J1, J2]
        rw [← exp_mul, ← exp_mul, ← exp_add, ← exp_add]
        exact exp_le_exp.mpr (by nlinarith [hg])
      have hsum := sum_mul_rpow_mul_rpow_le Finset.univ (prodWeight p) J1 J2
        (prodWeight_nonneg hp0) (fun _ => (exp_pos _).le) (fun _ => (exp_pos _).le) hl0 hl1
      set S1 := ∑ x, prodWeight p x * J1 x
      set S2 := ∑ x, prodWeight p x * J2 x
      have hS1 : 0 ≤ S1 :=
        Finset.sum_nonneg fun x _ => mul_nonneg (prodWeight_nonneg hp0 x) (exp_pos _).le
      have hS2 : 0 ≤ S2 :=
        Finset.sum_nonneg fun x _ => mul_nonneg (prodWeight_nonneg hp0 x) (exp_pos _).le
      have ih1 : S1 * α ω ≤ 1 := ih (sectionAt A ω)
      have ih2 : S2 * β ≤ 1 := ih B
      have hS2le : S2 ≤ 1 / β := by rw [le_div_iff₀ hβ]; exact ih2
      have hkey : exp ((1 - l) ^ 2 / 4) * (S1 ^ l * S2 ^ (1 - l)) ≤ (2 - r) / β := by
        rcases hl0.lt_or_eq with hlpos | hl
        · have hr : 0 < r := hlr.resolve_left hlpos.ne'
          have hα : 0 < α ω := hαpos hr
          have hS1le : S1 ≤ 1 / α ω := by rw [le_div_iff₀ hα]; exact ih1
          have h1 : S1 ^ l ≤ (1 / α ω) ^ l := rpow_le_rpow hS1 hS1le hl0
          have h2 : S2 ^ (1 - l) ≤ (1 / β) ^ (1 - l) := rpow_le_rpow hS2 hS2le (by linarith)
          have hprod : S1 ^ l * S2 ^ (1 - l) ≤ (1 / α ω) ^ l * (1 / β) ^ (1 - l) :=
            mul_le_mul h1 h2 (rpow_nonneg hS2 _) (rpow_nonneg (by positivity) _)
          have hid : r ^ l * ((1 / α ω) ^ l * (1 / β) ^ (1 - l)) = 1 / β := by
            rw [← mul_assoc, ← mul_rpow hr0 (by positivity)]
            have : r * (1 / α ω) = 1 / β := by
              rw [hrdef]; field_simp
            rw [this, ← rpow_add (by positivity), add_sub_cancel, rpow_one]
          calc exp ((1 - l) ^ 2 / 4) * (S1 ^ l * S2 ^ (1 - l))
              ≤ ((2 - r) * r ^ l) * ((1 / α ω) ^ l * (1 / β) ^ (1 - l)) :=
                mul_le_mul hexp hprod (by positivity) (by nlinarith [rpow_nonneg hr0 l])
            _ = (2 - r) * (r ^ l * ((1 / α ω) ^ l * (1 / β) ^ (1 - l))) := by ring
            _ = (2 - r) / β := by rw [hid]; ring
        · subst hl
          simp only [rpow_zero, mul_one, sub_zero, rpow_one, one_mul, one_pow] at hexp ⊢
          calc exp (1 / 4) * S2 ≤ (2 - r) * (1 / β) :=
                mul_le_mul (by simpa using hexp) hS2le hS2 (by linarith)
            _ = (2 - r) / β := by ring
      calc ∑ x : Fin N → Ω, prodWeight p x * exp (convexDistance A (Fin.cons ω x) ^ 2 / 4)
          ≤ ∑ x : Fin N → Ω, prodWeight p x *
              (exp ((1 - l) ^ 2 / 4) * (J1 x ^ l * J2 x ^ (1 - l))) :=
            Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (hpt x) (prodWeight_nonneg hp0 x)
        _ = exp ((1 - l) ^ 2 / 4) * ∑ x, prodWeight p x * (J1 x ^ l * J2 x ^ (1 - l)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        _ ≤ exp ((1 - l) ^ 2 / 4) * (S1 ^ l * S2 ^ (1 - l)) :=
            mul_le_mul_of_nonneg_left hsum (exp_pos _).le
        _ ≤ (2 - r) / β := hkey
    have hβne : β ≠ 0 := hβ.ne'
    set S := ∑ x, prodWeight p x * exp (convexDistance A x ^ 2 / 4)
    have hsplit : S = ∑ ω, p ω * ∑ x : Fin N → Ω,
        prodWeight p x * exp (convexDistance A (Fin.cons ω x) ^ 2 / 4) := by
      simp only [S]
      rw [sum_fin_succ_pi]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [prodWeight_cons]; ring
    have hSle : S ≤ (2 - weightOf p A / β) / β := by
      rw [hsplit]
      calc ∑ ω, p ω * ∑ x : Fin N → Ω,
              prodWeight p x * exp (convexDistance A (Fin.cons ω x) ^ 2 / 4)
          ≤ ∑ ω, p ω * ((2 - α ω / β) / β) :=
            Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hω ω) (hp0 ω)
        _ = (2 - weightOf p A / β) / β := by
            have : ∀ ω, p ω * ((2 - α ω / β) / β) = 2 / β * p ω - 1 / β ^ 2 * (p ω * α ω) :=
              fun ω => by field_simp
            rw [Finset.sum_congr rfl fun ω _ => this ω, Finset.sum_sub_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, hp1, ← hPA]
            field_simp
    calc S * weightOf p A ≤ (2 - weightOf p A / β) / β * weightOf p A :=
          mul_le_mul_of_nonneg_right hSle hPA0
      _ = (weightOf p A / β) * (2 - weightOf p A / β) := by ring
      _ ≤ 1 := by nlinarith [sq_nonneg (1 - weightOf p A / β)]

/-- **Tail form on a product of finite sets** (Talagrand, *Concentration of measure and
isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Theorem 4.1.1, (4.1.3),
for a finite `Ω`). Under the hypotheses of `sum_exp_convexDistance_mul_weightOf_le`, for every
`t ≥ 0`, `P(f_c(A, ·) ≥ t) · P(A) ≤ exp(-t² / 4)`. -/
theorem weightOf_le_convexDistance_mul_weightOf_le (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) (N : ℕ) (A : Set (Fin N → Ω)) {t : ℝ} (ht : 0 ≤ t) :
    weightOf p {x | t ≤ convexDistance A x} * weightOf p A ≤ exp (-t ^ 2 / 4) := by
  have hmain := sum_exp_convexDistance_mul_weightOf_le p hp0 hp1 N A
  have hmarkov : exp (t ^ 2 / 4) * weightOf p {x | t ≤ convexDistance A x} ≤
      ∑ x, prodWeight p x * exp (convexDistance A x ^ 2 / 4) := by
    rw [weightOf, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : t ≤ convexDistance A x
    · rw [Set.indicator_of_mem (show x ∈ {x | t ≤ convexDistance A x} from hx), mul_comm]
      refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (prodWeight_nonneg hp0 x)
      have := pow_le_pow_left₀ ht hx 2
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x | t ≤ convexDistance A x} from hx), mul_zero]
      exact mul_nonneg (prodWeight_nonneg hp0 x) (exp_pos _).le
  have hA := weightOf_nonneg hp0 A
  have h1 : exp (t ^ 2 / 4) * (weightOf p {x | t ≤ convexDistance A x} * weightOf p A) ≤ 1 := by
    calc exp (t ^ 2 / 4) * (weightOf p {x | t ≤ convexDistance A x} * weightOf p A)
        = (exp (t ^ 2 / 4) * weightOf p {x | t ≤ convexDistance A x}) * weightOf p A := by ring
      _ ≤ (∑ x, prodWeight p x * exp (convexDistance A x ^ 2 / 4)) * weightOf p A :=
          mul_le_mul_of_nonneg_right hmarkov hA
      _ ≤ 1 := hmain
  rw [show -t ^ 2 / 4 = -(t ^ 2 / 4) by ring, exp_neg, ← one_div, le_div_iff₀ (exp_pos _)]
  linarith

omit [Fintype Ω] in
open MeasureTheory in
/-- **The convex-distance inequality for a finite probability space, measure form** (Talagrand,
*Concentration of measure and isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81
(1995), Theorem 4.1.1, (4.1.2), for a finite `Ω`). For a probability measure `μ` on a finite set
`Ω` with measurable singletons and every `A ⊆ Ω^N`, with `P = μ^{⊗N}`:
`∫ exp(f_c(A, x)² / 4) dP(x) ≤ 1 / P(A)`. This is the finite case of
`MathlibExt.Probability.ConvexDistanceWanted.lintegral_exp_convexDistance_sq_le`. -/
theorem lintegral_exp_convexDistance_sq_le_of_fintype [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    (A : Set (Fin N → Ω)) :
    ∫⁻ x, ENNReal.ofReal (exp (convexDistance A x ^ 2 / 4)) ∂Measure.pi (fun _ => μ) ≤
      (Measure.pi (fun _ => μ) A)⁻¹ := by
  classical
  have := Fintype.ofFinite Ω
  set p : Ω → ℝ := fun ω => μ.real {ω}
  have hp0 : ∀ ω, 0 ≤ p ω := fun ω => MeasureTheory.measureReal_nonneg
  have hp1 : ∑ ω, p ω = 1 := by
    simp only [p]
    rw [MeasureTheory.sum_measureReal_singleton, Finset.coe_univ, MeasureTheory.probReal_univ]
  have hsing : ∀ x : Fin N → Ω, Measure.pi (fun _ => μ) {x} = ENNReal.ofReal (prodWeight p x) := by
    intro x
    rw [Measure.pi_singleton, prodWeight, ENNReal.ofReal_prod_of_nonneg (fun i _ => hp0 _)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [p]
    rw [MeasureTheory.ofReal_measureReal]
  have hint : ∫⁻ x, ENNReal.ofReal (exp (convexDistance A x ^ 2 / 4)) ∂Measure.pi (fun _ => μ) =
      ENNReal.ofReal (∑ x, prodWeight p x * exp (convexDistance A x ^ 2 / 4)) := by
    rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg
      (fun x _ => mul_nonneg (prodWeight_nonneg hp0 x) (exp_pos _).le)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsing, ENNReal.ofReal_mul (prodWeight_nonneg hp0 x), mul_comm]
  have hA : Measure.pi (fun _ => μ) A = ENNReal.ofReal (weightOf p A) := by
    have hmeas : MeasurableSet A := (Set.toFinite A).measurableSet
    rw [← lintegral_indicator_one hmeas, lintegral_fintype, weightOf,
      ENNReal.ofReal_sum_of_nonneg (fun x _ => by
        by_cases hx : x ∈ A <;> simp [Set.indicator, hx, prodWeight_nonneg hp0 x])]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx, hsing]
  have hmain := sum_exp_convexDistance_mul_weightOf_le p hp0 hp1 N A
  have hS0 : 0 ≤ ∑ x, prodWeight p x * exp (convexDistance A x ^ 2 / 4) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (prodWeight_nonneg hp0 x) (exp_pos _).le
  rw [hint, hA]
  rcases (weightOf_nonneg hp0 A).lt_or_eq with hpos | hzero
  · rw [← ENNReal.ofReal_inv_of_pos hpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← one_div, le_div_iff₀ hpos]
    exact hmain
  · rw [← hzero, ENNReal.ofReal_zero, ENNReal.inv_zero]
    exact le_top

end MathlibExt.Probability.ConvexDistance
