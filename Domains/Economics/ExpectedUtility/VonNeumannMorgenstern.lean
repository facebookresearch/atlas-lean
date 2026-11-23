/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Expected utility: the von Neumann–Morgenstern theorem for finitely many outcomes

Lotteries over a finite outcome type `X` are `Convexity.StdSimplex ℝ X`; the probability mixture
`mix α p q` is the pointwise convex combination `α p + (1 - α) q` (not a compound lottery). A
preference relation `R` on lotteries (`R p q` reads `p ≿ q`) that is complete and transitive and
satisfies independence and the Archimedean property has an expected-utility representation:
some `u : X → ℝ` with `p ≿ q ↔ E_q[u] ≤ E_p[u]`. No nondegeneracy is assumed; if all lotteries
are indifferent, a constant `u` works.

## Main definitions

* `mix`, `expectedUtility`, `StrictPref`.
* `IsPreferenceRelation`, `SatisfiesIndependence`, `SatisfiesArchimedean`: the axioms.
* `IsExpectedUtilityRepresentation`: `u` represents `R` in expected utility.

## Main results

* `exists_isExpectedUtilityRepresentation`: the expected-utility theorem.

## References

* J. von Neumann and O. Morgenstern, *Theory of Games and Economic Behavior*, 3rd ed.,
  Princeton University Press (1953).
* D. Gonçalves, *ECON0106 Microeconomics, 5. Expected Utility*, UCL lecture notes (2025):
  Definitions 1-3 and Theorem 1(i). The theorem there assumes vNM continuity; the Archimedean
  form used here is Definition 3(i), which with independence implies vNM continuity
  (Exercise 1(i)(b)).
-/

namespace MathlibExt.Economics.ExpectedUtility

open Convexity

/-- The probability mixture `α p + (1 - α) q` of two lotteries, `α ∈ [0, 1]` (Gonçalves,
Section 2): the pointwise convex combination of the weights, not a compound lottery. -/
noncomputable def mix {X : Type*} (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (p q : StdSimplex ℝ X) : StdSimplex ℝ X :=
  convexCombPair α (1 - α) h0 (sub_nonneg.2 h1) (by ring) p q

/-- Expected utility `E_p[u] = ∑ₓ p(x) u(x)` of a lottery `p` under a Bernoulli utility `u`
(Gonçalves, Definition 1). -/
def expectedUtility {X : Type*} [Fintype X] (u : X → ℝ) (p : StdSimplex ℝ X) : ℝ :=
  ∑ x, p.weights x * u x

/-- Strict preference `p ≻ q`: `p ≿ q` and not `q ≿ p`. -/
def StrictPref {X : Type*} (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (p q : StdSimplex ℝ X) : Prop :=
  R p q ∧ ¬ R q p

/-- `R` is a preference relation on lotteries: complete and transitive (Gonçalves, Section 2:
"let ≿ be a preference relation on Δ(X)"). `R p q` reads `p ≿ q`. -/
def IsPreferenceRelation {X : Type*} (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop) : Prop :=
  (∀ p q, R p q ∨ R q p) ∧ ∀ p q r, R p q → R q r → R p r

/-- Independence (Gonçalves, Definition 2): for lotteries `p q r` and `α ∈ (0, 1]`,
`p ≿ q ↔ α p + (1 - α) r ≿ α q + (1 - α) r`. The strict version follows. -/
def SatisfiesIndependence {X : Type*} (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop) : Prop :=
  ∀ (p q r : StdSimplex ℝ X) (α : ℝ) (h0 : 0 < α) (h1 : α ≤ 1),
    R p q ↔ R (mix α h0.le h1 p r) (mix α h0.le h1 q r)

/-- The Archimedean property (Gonçalves, Definition 3(i)): if `p ≻ q ≻ r`, there are
`α β ∈ (0, 1)` with `α p + (1 - α) r ≻ q ≻ β p + (1 - β) r`. -/
def SatisfiesArchimedean {X : Type*} (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop) : Prop :=
  ∀ p q r : StdSimplex ℝ X, StrictPref R p q → StrictPref R q r →
    ∃ (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1),
      StrictPref R (mix α hα0.le hα1.le p r) q ∧ StrictPref R q (mix β hβ0.le hβ1.le p r)

/-- `u : X → ℝ` is an expected-utility (Bernoulli) representation of `R`:
`p ≿ q ↔ E_p[u] ≥ E_q[u]` (Gonçalves, Definition 1). -/
def IsExpectedUtilityRepresentation {X : Type*} [Fintype X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop) (u : X → ℝ) : Prop :=
  ∀ p q, R p q ↔ expectedUtility u q ≤ expectedUtility u p

/-! ### Mixtures and expected utility -/

theorem mix_weights {X : Type*} (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (p q : StdSimplex ℝ X) :
    (mix α h0 h1 p q).weights = α • p.weights + (1 - α) • q.weights := by
  unfold mix
  rw [StdSimplex.weights_convexCombPair]

private theorem mix_apply {X : Type*} (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (p q : StdSimplex ℝ X) (x : X) :
    (mix α h0 h1 p q).weights x = α * p.weights x + (1 - α) * q.weights x := by
  rw [mix_weights]
  simp [Finsupp.add_apply, smul_eq_mul]

private theorem mix_proof_irrel {X : Type*} (α : ℝ) (h0 h0' : 0 ≤ α) (h1 h1' : α ≤ 1)
    (p q : StdSimplex ℝ X) : mix α h0 h1 p q = mix α h0' h1' p q := rfl

private theorem mix_self {X : Type*} (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (p : StdSimplex ℝ X) : mix α h0 h1 p p = p := by
  apply StdSimplex.ext
  rw [mix_weights]
  have h : α + (1 - α) = 1 := by ring
  rw [← add_smul, h, one_smul]

private theorem mix_comm {X : Type*} (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (p q : StdSimplex ℝ X) :
    mix α h0 h1 p q = mix (1 - α) (sub_nonneg.2 h1) (by linarith) q p := by
  apply StdSimplex.ext
  rw [mix_weights, mix_weights]
  have h : (1 : ℝ) - (1 - α) = α := by ring
  rw [h, add_comm]

theorem mix_one {X : Type*} (h0 : (0 : ℝ) ≤ 1) (h1 : (1 : ℝ) ≤ 1)
    (p q : StdSimplex ℝ X) : mix 1 h0 h1 p q = p := by
  apply StdSimplex.ext
  rw [mix_weights]
  simp

theorem mix_zero {X : Type*} (h0 : (0 : ℝ) ≤ 0) (h1 : (0 : ℝ) ≤ 1)
    (p q : StdSimplex ℝ X) : mix 0 h0 h1 p q = q := by
  apply StdSimplex.ext
  rw [mix_weights]
  simp

theorem expectedUtility_mix {X : Type*} [Fintype X] (u : X → ℝ)
    (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (p q : StdSimplex ℝ X) :
    expectedUtility u (mix α h0 h1 p q)
      = α * expectedUtility u p + (1 - α) * expectedUtility u q := by
  unfold expectedUtility
  have hpt : ∀ x : X, (mix α h0 h1 p q).weights x * u x
      = α * (p.weights x * u x) + (1 - α) * (q.weights x * u x) := by
    intro x
    rw [mix_apply]
    ring
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem mix_mix_W {X : Type*} (α a : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (B W : StdSimplex ℝ X) :
    mix α hα0 hα1 (mix a ha0 ha1 B W) W
      = mix (α * a) (mul_nonneg hα0 ha0)
        (by have h : α * a ≤ 1 * a := mul_le_mul_of_nonneg_right hα1 ha0
            rw [one_mul] at h
            exact le_trans h ha1) B W := by
  apply StdSimplex.ext
  ext x
  simp only [mix_apply]
  ring

private theorem mix_B_mix {X : Type*} (β a : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (B W : StdSimplex ℝ X) :
    mix β hβ0 hβ1 B (mix a ha0 ha1 B W)
      = mix (β + (1 - β) * a)
        (add_nonneg hβ0 (mul_nonneg (sub_nonneg.2 hβ1) ha0))
        (by have h : (1 - β) * a ≤ (1 - β) * 1 :=
              mul_le_mul_of_nonneg_left ha1 (sub_nonneg.2 hβ1)
            linarith) B W := by
  apply StdSimplex.ext
  ext x
  simp only [mix_apply]
  ring

private theorem mix_seg_seg {X : Type*} (β a c : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (B W : StdSimplex ℝ X) :
    mix β hβ0 hβ1 (mix a ha0 ha1 B W) (mix c hc0 hc1 B W)
      = mix (β * a + (1 - β) * c)
        (add_nonneg (mul_nonneg hβ0 ha0) (mul_nonneg (sub_nonneg.2 hβ1) hc0))
        (by have h1 : β * a ≤ β * 1 := mul_le_mul_of_nonneg_left ha1 hβ0
            have h2 : (1 - β) * c ≤ (1 - β) * 1 :=
              mul_le_mul_of_nonneg_left hc1 (sub_nonneg.2 hβ1)
            linarith) B W := by
  apply StdSimplex.ext
  ext x
  simp only [mix_apply]
  ring

private theorem mix_mono_key {X : Type*} (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : a < b) (B W : StdSimplex ℝ X) :
    mix b hb0 hb1 B W
      = mix ((b - a) / (1 - a))
        (le_of_lt (div_pos (sub_pos.mpr hab)
          (sub_pos.mpr (lt_of_lt_of_le hab hb1))))
        (by have h1a : (0 : ℝ) < 1 - a := sub_pos.mpr (lt_of_lt_of_le hab hb1)
            rw [div_le_one h1a]
            linarith)
        B (mix a ha0 ha1 B W) := by
  have h1a : (0 : ℝ) < 1 - a := sub_pos.mpr (lt_of_lt_of_le hab hb1)
  have hμ : ((b - a) / (1 - a)) * (1 - a) = b - a :=
    div_mul_cancel₀ _ (ne_of_gt h1a)
  apply StdSimplex.ext
  ext x
  simp only [mix_apply]
  linear_combination (W.weights x - B.weights x) * hμ

private theorem pref_refl {X : Type*} (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hR : IsPreferenceRelation R) (p : StdSimplex ℝ X) : R p p := by
  rcases hR.1 p p with h | h <;> exact h

private theorem exists_best_worst {X : Type*} [Finite X] [Nonempty X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop) (hR : IsPreferenceRelation R) :
    ∃ xb xw, (∀ x, R (StdSimplex.single xb) (StdSimplex.single x)) ∧
             (∀ x, R (StdSimplex.single x) (StdSimplex.single xw)) := by
  have := Fintype.ofFinite X
  classical
  have best : ∀ (s : Finset X), s.Nonempty →
      ∃ b ∈ s, ∀ x ∈ s, R (StdSimplex.single b) (StdSimplex.single x) := by
    intro s
    induction s using Finset.induction with
    | empty => intro hs; exact (Finset.not_nonempty_empty hs).elim
    | @insert a s ha ih =>
      intro hs
      by_cases hsne : s.Nonempty
      · obtain ⟨b, hb, hbest⟩ := ih hsne
        rcases hR.1 (StdSimplex.single a) (StdSimplex.single b) with h | h
        · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact pref_refl R hR _
          · exact hR.2 _ _ _ h (hbest x hx)
        · refine ⟨b, Finset.mem_insert_of_mem hb, fun x hx => ?_⟩
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact h
          · exact hbest x hx
      · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact pref_refl R hR _
        · exact absurd ⟨x, hx⟩ hsne
  have worst : ∀ (s : Finset X), s.Nonempty →
      ∃ w ∈ s, ∀ x ∈ s, R (StdSimplex.single x) (StdSimplex.single w) := by
    intro s
    induction s using Finset.induction with
    | empty => intro hs; exact (Finset.not_nonempty_empty hs).elim
    | @insert a s ha ih =>
      intro hs
      by_cases hsne : s.Nonempty
      · obtain ⟨b, hb, hworst⟩ := ih hsne
        rcases hR.1 (StdSimplex.single a) (StdSimplex.single b) with h | h
        · refine ⟨b, Finset.mem_insert_of_mem hb, fun x hx => ?_⟩
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact h
          · exact hworst x hx
        · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact pref_refl R hR _
          · exact hR.2 _ _ _ (hworst x hx) h
      · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact pref_refl R hR _
        · exact absurd ⟨x, hx⟩ hsne
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨xb, -, hxb⟩ := best Finset.univ ⟨x0, Finset.mem_univ x0⟩
  obtain ⟨xw, -, hxw⟩ := worst Finset.univ ⟨x0, Finset.mem_univ x0⟩
  exact ⟨xb, xw, fun x => hxb x (Finset.mem_univ x),
    fun x => hxw x (Finset.mem_univ x)⟩

private theorem exists_mix_single_of_card {X : Type*} [Finite X]
    (p : StdSimplex ℝ X) (hcard : 2 ≤ p.weights.support.card) :
    ∃ (x : X) (q : StdSimplex ℝ X) (α : ℝ) (h0 : 0 < α) (h1 : α < 1),
      p.weights x = α ∧ x ∈ p.weights.support ∧
      p = mix α h0.le h1.le (StdSimplex.single x) q ∧
      q.weights.support.card < p.weights.support.card := by
  have := Fintype.ofFinite X
  classical
  obtain ⟨x, hx⟩ := p.support_weights_nonempty
  have hwx : p.weights x ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hpos_x : 0 < p.weights x :=
    (p.weights_nonneg x).lt_of_ne (Ne.symm hwx)
  have h2 : 1 < p.weights.support.card := by omega
  rw [Finset.one_lt_card] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := h2
  have hne : ∃ w ∈ p.weights.support, w ≠ x := by
    by_cases hxy : y = x
    · exact ⟨z, hz, by rw [← hxy]; exact Ne.symm hyz⟩
    · exact ⟨y, hy, hxy⟩
  obtain ⟨w, hw, hwx_ne⟩ := hne
  have hpos_w : 0 < p.weights w :=
    (p.weights_nonneg w).lt_of_ne (Ne.symm (Finsupp.mem_support_iff.mp hw))
  have hsum2 : p.weights x + p.weights w ≤ ∑ i, p.weights i := by
    have hsub : ({x, w} : Finset X) ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => p.weights_nonneg i)
    rw [Finset.sum_pair (Ne.symm hwx_ne)] at hle
    exact hle
  have htot := p.total_of_fintype
  have hlt1 : p.weights x < 1 := by
    have : p.weights x + p.weights w ≤ 1 := by rw [← htot]; exact hsum2
    linarith
  set α : ℝ := p.weights x with hα
  have hs : ∃ a ∈ ({x} : Set X), p.weights a ≠ 0 :=
    ⟨x, Set.mem_singleton_iff.mpr rfl, hwx⟩
  have hs' : ∃ a ∈ ({x}ᶜ : Set X), p.weights a ≠ 0 :=
    ⟨w, by simpa using hwx_ne, Finsupp.mem_support_iff.mp hw⟩
  set q : StdSimplex ℝ X := p.restrict ({x}ᶜ : Set X) hs' with hq
  refine ⟨x, q, α, hpos_x, hlt1, rfl, hx, ?_, ?_⟩
  · have hrr := StdSimplex.convexCombPair_restrict_restrict_compl p ({x} : Set X) hs hs'
    have hsing : p.restrict ({x} : Set X) hs = StdSimplex.single x :=
      StdSimplex.restrict_singleton p x hs
    have hfilter : p.weights.filter (· ∈ ({x} : Set X))
        = Finsupp.single x (p.weights x) := by
      ext z
      by_cases hz : z = x
      · subst hz
        simp
      · simp [hz]
    have hSx : ((p.weights.filter (· ∈ ({x} : Set X))).sum fun _ k => k) = α := by
      rw [hfilter]
      exact Finsupp.sum_single_index rfl
    have hpart := Finsupp.sum_filter_add_sum_filter_not (· ∈ ({x} : Set X))
      p.weights (fun _ k => k)
    have hSy : ((p.weights.filter (· ∉ ({x} : Set X))).sum fun _ k => k) = 1 - α := by
      have h1 := p.total
      rw [hSx] at hpart
      linarith
    apply StdSimplex.ext
    have hw := congrArg StdSimplex.weights hrr
    rw [StdSimplex.weights_convexCombPair, hsing, hSx, hSy] at hw
    rw [mix_weights]
    exact hw.symm
  · have hsupp := StdSimplex.support_weights_restrict p ({x}ᶜ : Set X) hs'
    rw [hsupp]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨x, hx, by simp⟩

private theorem simplex_strong_induction {X : Type*} [Finite X]
    (P : StdSimplex ℝ X → Prop)
    (single_case : ∀ x : X, P (StdSimplex.single x))
    (mix_case : ∀ (x : X) (q : StdSimplex ℝ X) (α : ℝ) (h0 : 0 < α) (h1 : α < 1),
      P q → P (mix α h0.le h1.le (StdSimplex.single x) q)) :
    ∀ p, P p := by
  have := Fintype.ofFinite X
  classical
  suffices H : ∀ (n : ℕ) (p : StdSimplex ℝ X), p.weights.support.card ≤ n → P p from
    fun p => H _ p le_rfl
  intro n
  induction n with
  | zero =>
    intro p hc
    have hpos : 0 < p.weights.support.card :=
      Finset.card_pos.mpr p.support_weights_nonempty
    omega
  | succ n ih =>
    intro p hc
    by_cases h1 : p.weights.support.card ≤ 1
    · have hpos : 0 < p.weights.support.card :=
        Finset.card_pos.mpr p.support_weights_nonempty
      have hcard : p.weights.support.card = 1 := by omega
      obtain ⟨x, hxs⟩ := Finset.card_eq_one.mp hcard
      have hpx : p = StdSimplex.single x :=
        StdSimplex.support_weights_eq_singleton.mp hxs
      rw [hpx]
      exact single_case x
    · have h2 : 1 < p.weights.support.card := not_le.mp h1
      obtain ⟨x, q, α, h0, h1', -, -, hpq, hlt⟩ :=
        exists_mix_single_of_card p (by omega)
      rw [hpq]
      exact mix_case x q α h0 h1' (ih q (by omega))

private theorem independence_right {X : Type*} (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hI : SatisfiesIndependence R)
    (p q r : StdSimplex ℝ X) (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    R p q ↔ R (mix α h0.le h1.le r p) (mix α h0.le h1.le r q) := by
  have e1 := mix_comm α h0.le h1.le r p
  have e2 := mix_comm α h0.le h1.le r q
  rw [e1, e2]
  exact hI p q r (1 - α) (sub_pos.mpr h1) (sub_le_self 1 h0.le)

private theorem all_indifferent_of_singles {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (B : StdSimplex ℝ X)
    (hsing : ∀ x : X, R (StdSimplex.single x) B ∧ R B (StdSimplex.single x)) :
    ∀ p q : StdSimplex ℝ X, R p q ∧ R q p := by
  have := Fintype.ofFinite X
  have hPB : ∀ p, R p B ∧ R B p := by
    apply simplex_strong_induction
    · intro x
      exact hsing x
    · intro x q α h0 h1 hq
      have eB : B = mix α h0.le h1.le B B := (mix_self α h0.le h1.le B).symm
      constructor
      · rw [eB]
        have s1 := (hI (StdSimplex.single x) B q α h0 h1.le).mp (hsing x).1
        have s2 := (independence_right R hI q B B α h0 h1).mp hq.1
        exact hR.2 _ _ _ s1 s2
      · rw [eB]
        have s1 := (hI B (StdSimplex.single x) B α h0 h1.le).mp (hsing x).2
        have s2 := (independence_right R hI B q (StdSimplex.single x) α h0 h1).mp hq.2
        exact hR.2 _ _ _ s1 s2
  intro p q
  exact ⟨hR.2 _ _ _ (hPB p).1 (hPB q).2, hR.2 _ _ _ (hPB q).1 (hPB p).2⟩

private theorem best_worst_bounds {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (B W : StdSimplex ℝ X)
    (hB : ∀ x : X, R B (StdSimplex.single x))
    (hW : ∀ x : X, R (StdSimplex.single x) W) :
    ∀ p : StdSimplex ℝ X, R B p ∧ R p W := by
  have := Fintype.ofFinite X
  apply simplex_strong_induction
  · intro x
    exact ⟨hB x, hW x⟩
  · intro x q α h0 h1 hq
    have eB : B = mix α h0.le h1.le B B := (mix_self α h0.le h1.le B).symm
    have eW : W = mix α h0.le h1.le W W := (mix_self α h0.le h1.le W).symm
    constructor
    · rw [eB]
      have s1 := (hI B (StdSimplex.single x) B α h0 h1.le).mp (hB x)
      have s2 := (independence_right R hI B q (StdSimplex.single x) α h0 h1).mp hq.1
      exact hR.2 _ _ _ s1 s2
    · rw [eW]
      have s1 := (hI (StdSimplex.single x) W q α h0 h1.le).mp (hW x)
      have s2 := (independence_right R hI q W W α h0 h1).mp hq.2
      exact hR.2 _ _ _ s1 s2

private theorem seg_gt_W {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (_hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (B W : StdSimplex ℝ X)
    (hbounds : ∀ p, R B p ∧ R p W)
    (hstrict : R B W ∧ ¬ R W B) :
    ∀ (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1), 0 < a →
      StrictPref R (mix a h0 h1 B W) W := by
  have := Fintype.ofFinite X
  intro a h0 h1 ha
  constructor
  · exact (hbounds _).2
  · intro hcon
    have eW : W = mix a ha.le h1 W W := (mix_self a ha.le h1 W).symm
    have hmix : R (mix a ha.le h1 W W) (mix a ha.le h1 B W) := by
      rw [← eW]
      exact hcon
    have hback := (hI W B W a ha h1).mpr hmix
    exact hstrict.2 hback

private theorem seg_lt_B {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (_hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (B W : StdSimplex ℝ X)
    (hbounds : ∀ p, R B p ∧ R p W)
    (hstrict : R B W ∧ ¬ R W B) :
    ∀ (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1), a < 1 →
      StrictPref R B (mix a h0 h1 B W) := by
  have := Fintype.ofFinite X
  intro a h0 h1 ha
  constructor
  · exact (hbounds _).1
  · intro hcon
    have eB : B = mix a h0 h1 B B := (mix_self a h0 h1 B).symm
    have hmix : R (mix a h0 h1 B W) (mix a h0 h1 B B) := by
      rw [← eB]
      exact hcon
    have f1 := mix_comm a h0 h1 B W
    have f2 := mix_comm a h0 h1 B B
    rw [f1, f2] at hmix
    have hback := (hI W B B (1 - a) (sub_pos.mpr ha) (sub_le_self 1 h0)).mpr hmix
    exact hstrict.2 hback

private theorem seg_strict_mono {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (B W : StdSimplex ℝ X)
    (hbounds : ∀ p, R B p ∧ R p W)
    (hstrict : R B W ∧ ¬ R W B) :
    ∀ (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1),
      a < b → StrictPref R (mix b hb0 hb1 B W) (mix a ha0 ha1 B W) := by
  have := Fintype.ofFinite X
  intro a b ha0 ha1 hb0 hb1 hab
  have ha1' : a < 1 := lt_of_lt_of_le hab hb1
  have h1a : (0 : ℝ) < 1 - a := sub_pos.mpr ha1'
  have hμ0 : 0 < (b - a) / (1 - a) := div_pos (sub_pos.mpr hab) h1a
  have hμ1 : (b - a) / (1 - a) ≤ 1 := by
    rw [div_le_one h1a]
    linarith
  have hBmid := seg_lt_B R hR hI B W hbounds hstrict a ha0 ha1 ha1'
  have hkey := mix_mono_key a b ha0 ha1 hb0 hb1 hab B W
  constructor
  · have h := (hI B (mix a ha0 ha1 B W) (mix a ha0 ha1 B W)
      _ hμ0 hμ1).mp hBmid.1
    rw [mix_self _ hμ0.le hμ1 (mix a ha0 ha1 B W)] at h
    rw [hkey]
    exact h
  · intro hcon
    rw [hkey] at hcon
    have e : mix a ha0 ha1 B W
        = mix _ hμ0.le hμ1 (mix a ha0 ha1 B W) (mix a ha0 ha1 B W) :=
      (mix_self _ hμ0.le hμ1 _).symm
    nth_rewrite 1 [e] at hcon
    have hback := (hI (mix a ha0 ha1 B W) B (mix a ha0 ha1 B W)
      _ hμ0 hμ1).mpr hcon
    exact hBmid.2 hback

private theorem seg_upper_cont {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (hA : SatisfiesArchimedean R)
    (B W : StdSimplex ℝ X)
    (hbounds : ∀ p, R B p ∧ R p W)
    (hstrict : R B W ∧ ¬ R W B) :
    ∀ (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) (p : StdSimplex ℝ X), 0 < a →
      StrictPref R (mix a h0 h1 B W) p →
      ∃ (a' : ℝ) (h0' : 0 ≤ a') (h1' : a' ≤ 1),
        a' < a ∧ StrictPref R (mix a' h0' h1' B W) p := by
  have := Fintype.ofFinite X
  intro a h0 h1 p ha hfa
  by_cases hpW : StrictPref R p W
  · obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hα, -⟩ :=
      hA (mix a h0 h1 B W) p W hfa hpW
    have hred := mix_mix_W α a hα0.le hα1.le h0 h1 B W
    rw [hred] at hα
    have ha0' : (0 : ℝ) ≤ α * a := mul_nonneg hα0.le h0
    have ha1' : α * a ≤ 1 := by
      have h : α * a ≤ 1 * a := mul_le_mul_of_nonneg_right hα1.le h0
      rw [one_mul] at h
      exact le_trans h h1
    have hlt : α * a < a := by
      have h := mul_lt_mul_of_pos_right hα1 ha
      rwa [one_mul] at h
    exact ⟨α * a, ha0', ha1', hlt, hα⟩
  · have hWp : R W p := by
      by_contra hc
      exact hpW ⟨(hbounds p).2, hc⟩
    have ha2 : (0 : ℝ) < a / 2 := by linarith
    have ha2le : a / 2 ≤ 1 := by linarith
    have hseg := seg_gt_W R hR hI B W hbounds hstrict (a / 2) ha2.le ha2le ha2
    refine ⟨a / 2, ha2.le, ha2le, by linarith, ?_⟩
    constructor
    · exact hR.2 _ _ _ hseg.1 hWp
    · intro hc
      exact hseg.2 (hR.2 _ _ _ hWp hc)

private theorem seg_lower_cont {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (hA : SatisfiesArchimedean R)
    (B W : StdSimplex ℝ X)
    (hbounds : ∀ p, R B p ∧ R p W)
    (hstrict : R B W ∧ ¬ R W B) :
    ∀ (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) (p : StdSimplex ℝ X), a < 1 →
      StrictPref R p (mix a h0 h1 B W) →
      ∃ (a' : ℝ) (h0' : 0 ≤ a') (h1' : a' ≤ 1),
        a < a' ∧ StrictPref R p (mix a' h0' h1' B W) := by
  have := Fintype.ofFinite X
  intro a h0 h1 p ha hfa
  by_cases hBp : StrictPref R B p
  · obtain ⟨α, β, hα0, hα1, hβ0, hβ1, -, hβ⟩ :=
      hA B p (mix a h0 h1 B W) hBp hfa
    have hred := mix_B_mix β a hβ0.le hβ1.le h0 h1 B W
    rw [hred] at hβ
    have h1a : (0 : ℝ) < 1 - a := sub_pos.mpr ha
    have hb0' : (0 : ℝ) ≤ β + (1 - β) * a :=
      add_nonneg hβ0.le (mul_nonneg (sub_nonneg.2 hβ1.le) h0)
    have hb1' : β + (1 - β) * a ≤ 1 := by
      have h : (1 - β) * a ≤ (1 - β) * 1 :=
        mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hβ1.le)
      linarith
    have hlt : a < β + (1 - β) * a := by
      have hpos := mul_pos hβ0 h1a
      have e : β + (1 - β) * a = a + β * (1 - a) := by ring
      rw [e]
      linarith
    exact ⟨β + (1 - β) * a, hb0', hb1', hlt, hβ⟩
  · have hpB : R p B := by
      by_contra hc
      exact hBp ⟨(hbounds p).1, hc⟩
    have ha2 : (a + 1) / 2 < 1 := by linarith
    have ha2ge : (0 : ℝ) ≤ (a + 1) / 2 := by linarith
    have hseg := seg_lt_B R hR hI B W hbounds hstrict ((a + 1) / 2) ha2ge ha2.le ha2
    refine ⟨(a + 1) / 2, ha2ge, ha2.le, by linarith, ?_⟩
    constructor
    · exact hR.2 _ _ _ hpB hseg.1
    · intro hc
      exact hseg.2 (hR.2 _ _ _ hc hpB)

private theorem exists_calibration {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (hA : SatisfiesArchimedean R)
    (B W : StdSimplex ℝ X)
    (hbounds : ∀ p, R B p ∧ R p W)
    (hstrict : R B W ∧ ¬ R W B) (p : StdSimplex ℝ X) :
    ∃ (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1),
      R p (mix γ h0 h1 B W) ∧ R (mix γ h0 h1 B W) p ∧
      ∀ (γ' : ℝ) (h0' : 0 ≤ γ') (h1' : γ' ≤ 1),
        R p (mix γ' h0' h1' B W) → R (mix γ' h0' h1' B W) p → γ' = γ := by
  have := Fintype.ofFinite X
  set L : Set ℝ := {a | ∃ (h0 : 0 ≤ a) (h1 : a ≤ 1), R p (mix a h0 h1 B W)} with hLdef
  set U : Set ℝ := {a | ∃ (h0 : 0 ≤ a) (h1 : a ≤ 1), R (mix a h0 h1 B W) p} with hUdef
  have hmono : ∀ (a a' : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha0' : 0 ≤ a') (ha1' : a' ≤ 1),
      a' ≤ a → R (mix a ha0 ha1 B W) (mix a' ha0' ha1' B W) := by
    intro a a' ha0 ha1 ha0' ha1' hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · subst heq
      exact pref_refl R hR _
    · exact (seg_strict_mono R hR hI B W hbounds hstrict a' a ha0' ha1' ha0 ha1 hlt).1
  have h0mem : (0 : ℝ) ∈ L := by
    change ∃ (h0 : (0 : ℝ) ≤ 0) (h1 : (0 : ℝ) ≤ 1), R p (mix 0 h0 h1 B W)
    refine ⟨le_rfl, zero_le_one, ?_⟩
    have e : mix 0 le_rfl zero_le_one B W = W := mix_zero le_rfl zero_le_one B W
    rw [e]
    exact (hbounds p).2
  have h1mem : (1 : ℝ) ∈ U := by
    change ∃ (h0 : (0 : ℝ) ≤ 1) (h1 : (1 : ℝ) ≤ 1), R (mix 1 h0 h1 B W) p
    refine ⟨zero_le_one, le_rfl, ?_⟩
    have e : mix 1 zero_le_one le_rfl B W = B := mix_one zero_le_one le_rfl B W
    rw [e]
    exact (hbounds p).1
  have hLne : L.Nonempty := ⟨0, h0mem⟩
  have hUne : U.Nonempty := ⟨1, h1mem⟩
  have hLbdd : BddAbove L := by
    refine ⟨1, ?_⟩
    intro a ha
    obtain ⟨-, ha1, -⟩ := ha
    exact ha1
  have hUbdd : BddBelow U := by
    refine ⟨0, ?_⟩
    intro a ha
    obtain ⟨ha0, -, -⟩ := ha
    exact ha0
  have hcover : ∀ (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1), a ∈ L ∨ a ∈ U := by
    intro a ha0 ha1
    rcases hR.1 p (mix a ha0 ha1 B W) with h | h
    · exact Or.inl ⟨ha0, ha1, h⟩
    · exact Or.inr ⟨ha0, ha1, h⟩
  have hLU : ∀ a ∈ L, ∀ b ∈ U, a ≤ b := by
    intro a ha b hb
    obtain ⟨ha0, ha1, hpa⟩ := ha
    obtain ⟨hb0, hb1, hbp⟩ := hb
    by_contra hlt
    have hlt' : b < a := lt_of_not_ge hlt
    have hst := seg_strict_mono R hR hI B W hbounds hstrict b a hb0 hb1 ha0 ha1 hlt'
    exact hst.2 (hR.2 _ _ _ hbp hpa)
  have hsup_le : sSup L ≤ sInf U := by
    apply csSup_le hLne
    intro a ha
    apply le_csInf hUne
    intro b hb
    exact hLU a ha b hb
  have hinf_le : sInf U ≤ sSup L := by
    by_contra hlt
    have hlt' : sSup L < sInf U := lt_of_not_ge hlt
    obtain ⟨a, hsa, hai⟩ := exists_between hlt'
    have h0a : (0 : ℝ) ≤ a := le_trans (le_csSup hLbdd h0mem) (le_of_lt hsa)
    have ha1 : a ≤ 1 := le_trans (le_of_lt hai) (csInf_le hUbdd h1mem)
    rcases hcover a h0a ha1 with haL | haU
    · have hle := le_csSup hLbdd haL
      linarith
    · have hle := csInf_le hUbdd haU
      linarith
  have hsup_inf : sSup L = sInf U := le_antisymm hsup_le hinf_le
  have hγ0 : (0 : ℝ) ≤ sSup L := le_csSup hLbdd h0mem
  have hγ1 : sSup L ≤ 1 := by
    apply csSup_le hLne
    intro b hb
    obtain ⟨-, hb1, -⟩ := hb
    exact hb1
  have hγL : sSup L ∈ L := by
    by_contra hγneg
    have hnpos : 0 < sSup L := by
      by_contra hc
      have hγ0eq : sSup L = 0 := le_antisymm (le_of_not_gt hc) hγ0
      have hmem : sSup L ∈ L := by rw [hγ0eq]; exact h0mem
      exact hγneg hmem
    have hnR : ¬ R p (mix (sSup L) hγ0 hγ1 B W) := fun h => hγneg ⟨hγ0, hγ1, h⟩
    have hR2 : R (mix (sSup L) hγ0 hγ1 B W) p := by
      rcases hR.1 p (mix (sSup L) hγ0 hγ1 B W) with h | h
      · exact absurd (⟨hγ0, hγ1, h⟩ : sSup L ∈ L) hγneg
      · exact h
    obtain ⟨a', h0', h1', hlt, hstr⟩ :=
      seg_upper_cont R hR hI hA B W hbounds hstrict (sSup L) hγ0 hγ1 p hnpos ⟨hR2, hnR⟩
    have haU : a' ∈ U := ⟨h0', h1', hstr.1⟩
    have hle := csInf_le hUbdd haU
    rw [← hsup_inf] at hle
    linarith
  have hγU : sSup L ∈ U := by
    by_contra hγneg
    have hnlt1 : sSup L < 1 := by
      by_contra hc
      have hγ1eq : sSup L = 1 := le_antisymm hγ1 (le_of_not_gt hc)
      have hmem : sSup L ∈ U := by rw [hγ1eq]; exact h1mem
      exact hγneg hmem
    have hnR : ¬ R (mix (sSup L) hγ0 hγ1 B W) p := fun h => hγneg ⟨hγ0, hγ1, h⟩
    have hR2 : R p (mix (sSup L) hγ0 hγ1 B W) := by
      rcases hR.1 p (mix (sSup L) hγ0 hγ1 B W) with h | h
      · exact h
      · exact absurd (⟨hγ0, hγ1, h⟩ : sSup L ∈ U) hγneg
    obtain ⟨a', h0', h1', hlt, hstr⟩ :=
      seg_lower_cont R hR hI hA B W hbounds hstrict (sSup L) hγ0 hγ1 p hnlt1 ⟨hR2, hnR⟩
    have haL : a' ∈ L := ⟨h0', h1', hstr.1⟩
    have hle := le_csSup hLbdd haL
    linarith
  obtain ⟨g0, g1, hpγ⟩ := hγL
  obtain ⟨g0', g1', hγp⟩ := hγU
  have hpγ' : R p (mix (sSup L) hγ0 hγ1 B W) := hpγ
  have hγp' : R (mix (sSup L) hγ0 hγ1 B W) p := hγp
  refine ⟨sSup L, hγ0, hγ1, hpγ', hγp', ?_⟩
  intro γ' h0' h1' hpq hqp
  have hL' : γ' ∈ L := ⟨h0', h1', hpq⟩
  have hU' : γ' ∈ U := ⟨h0', h1', hqp⟩
  have hle1 : γ' ≤ sSup L := le_csSup hLbdd hL'
  have hle2 : sSup L ≤ γ' := by
    have h := csInf_le hUbdd hU'
    rw [← hsup_inf] at h
    exact h
  exact le_antisymm hle1 hle2

private theorem seg_mono_le {X : Type*} [Finite X]
    (R : StdSimplex ℝ X → StdSimplex ℝ X → Prop)
    (hR : IsPreferenceRelation R) (hI : SatisfiesIndependence R)
    (B W : StdSimplex ℝ X)
    (hbounds : ∀ p, R B p ∧ R p W)
    (hstrict : R B W ∧ ¬ R W B) :
    ∀ (a a' : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha0' : 0 ≤ a') (ha1' : a' ≤ 1),
      a' ≤ a → R (mix a ha0 ha1 B W) (mix a' ha0' ha1' B W) := by
  have := Fintype.ofFinite X
  intro a a' ha0 ha1 ha0' ha1' hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    exact pref_refl R hR _
  · exact (seg_strict_mono R hR hI B W hbounds hstrict a' a ha0' ha1' ha0 ha1 hlt).1

/-- Expected utility of a point mass is the utility of that outcome. -/
theorem expectedUtility_single {X : Type*} [Fintype X] (u : X → ℝ) (x : X) :
    expectedUtility u (StdSimplex.single x) = u x := by
  unfold expectedUtility
  rw [StdSimplex.weights_single]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    rw [Finsupp.single_eq_of_ne hy]
    exact zero_mul _
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- Expected-utility theorem for finitely many outcomes: a preference relation on lotteries that
satisfies independence and the Archimedean property has an expected-utility representation. -/
theorem exists_isExpectedUtilityRepresentation {X : Type*} [Fintype X]
    {R : StdSimplex ℝ X → StdSimplex ℝ X → Prop} (hR : IsPreferenceRelation R)
    (hI : SatisfiesIndependence R) (hA : SatisfiesArchimedean R) :
    ∃ u : X → ℝ, IsExpectedUtilityRepresentation R u := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have := hX
    have : IsEmpty (StdSimplex ℝ X) :=
      ⟨fun w => by obtain ⟨x⟩ := w.nonempty; exact isEmptyElim x⟩
    exact ⟨0, fun p _ => isEmptyElim p⟩
  · have := hX
    obtain ⟨xb, xw, hxb, hxw⟩ := exists_best_worst R hR
    set B : StdSimplex ℝ X := StdSimplex.single xb with hBdef
    set W : StdSimplex ℝ X := StdSimplex.single xw with hWdef
    by_cases hind : R W B
    · have hsing : ∀ x : X, R (StdSimplex.single x) B ∧ R B (StdSimplex.single x) := by
        intro x
        exact ⟨hR.2 _ _ _ (hxw x) hind, hxb x⟩
      have hall := all_indifferent_of_singles R hR hI B hsing
      refine ⟨0, ?_⟩
      intro p q
      have hEU : expectedUtility (0 : X → ℝ) q ≤ expectedUtility (0 : X → ℝ) p := by
        simp [expectedUtility]
      exact ⟨fun _ => hEU, fun _ => (hall p q).1⟩
    · have hstrict : R B W ∧ ¬ R W B := ⟨hxb xw, hind⟩
      have hbounds := best_worst_bounds R hR hI B W (fun x => hxb x) (fun x => hxw x)
      have hcal := exists_calibration R hR hI hA B W hbounds hstrict
      choose γ hγ0 hγ1 hγspec using hcal
      have haff : ∀ (p q : StdSimplex ℝ X) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1),
          γ (mix α h0 h1 p q) = α * γ p + (1 - α) * γ q := by
        intro p q α h0 h1
        by_cases hα0 : α = 0
        · subst hα0
          rw [mix_zero _ _ p q]
          simp
        · by_cases hα1 : α = 1
          · subst hα1
            rw [mix_one _ _ p q]
            simp
          · have ha0 : 0 < α := h0.lt_of_ne (Ne.symm hα0)
            have ha1 : α < 1 := h1.lt_of_ne hα1
            have hc0 : (0 : ℝ) ≤ α * γ p + (1 - α) * γ q :=
              add_nonneg (mul_nonneg h0 (hγ0 p)) (mul_nonneg (sub_nonneg.2 h1) (hγ0 q))
            have hc1 : α * γ p + (1 - α) * γ q ≤ 1 := by
              have e1 : α * γ p ≤ α * 1 := mul_le_mul_of_nonneg_left (hγ1 p) h0
              have e2 : (1 - α) * γ q ≤ (1 - α) * 1 :=
                mul_le_mul_of_nonneg_left (hγ1 q) (sub_nonneg.2 h1)
              rw [mul_one] at e1 e2
              linarith
            have hred := mix_seg_seg α (γ p) (γ q) h0 h1 (hγ0 p) (hγ1 p)
              (hγ0 q) (hγ1 q) B W
            have h1a : R (mix α h0 h1 p q)
                (mix α h0 h1 (mix (γ p) (hγ0 p) (hγ1 p) B W)
                  (mix (γ q) (hγ0 q) (hγ1 q) B W)) := by
              have s1 := (hI p (mix (γ p) (hγ0 p) (hγ1 p) B W) q α ha0 h1).mp
                (hγspec p).1
              have s2 := (independence_right R hI q (mix (γ q) (hγ0 q) (hγ1 q) B W)
                (mix (γ p) (hγ0 p) (hγ1 p) B W) α ha0 ha1).mp (hγspec q).1
              exact hR.2 _ _ _ s1 s2
            have h1b : R (mix α h0 h1 (mix (γ p) (hγ0 p) (hγ1 p) B W)
                  (mix (γ q) (hγ0 q) (hγ1 q) B W)) (mix α h0 h1 p q) := by
              have s1 := (hI (mix (γ p) (hγ0 p) (hγ1 p) B W) p
                (mix (γ q) (hγ0 q) (hγ1 q) B W) α ha0 h1).mp (hγspec p).2.1
              have s2 := (independence_right R hI (mix (γ q) (hγ0 q) (hγ1 q) B W) q p
                α ha0 ha1).mp (hγspec q).2.1
              exact hR.2 _ _ _ s1 s2
            rw [hred] at h1a h1b
            have huniq := (hγspec (mix α h0 h1 p q)).2.2
              (α * γ p + (1 - α) * γ q) hc0 hc1 h1a h1b
            exact huniq.symm
      have hγrep : ∀ p q, R p q ↔ γ q ≤ γ p := by
        intro p q
        constructor
        · intro hpq
          by_contra hlt
          have hlt' : γ p < γ q := lt_of_not_ge hlt
          have hst := seg_strict_mono R hR hI B W hbounds hstrict (γ p) (γ q)
            (hγ0 p) (hγ1 p) (hγ0 q) (hγ1 q) hlt'
          have htrans : R (mix (γ p) (hγ0 p) (hγ1 p) B W)
              (mix (γ q) (hγ0 q) (hγ1 q) B W) :=
            hR.2 _ _ _ (hR.2 _ _ _ (hγspec p).2.1 hpq) (hγspec q).1
          exact hst.2 htrans
        · intro hle
          have hmid : R (mix (γ p) (hγ0 p) (hγ1 p) B W)
              (mix (γ q) (hγ0 q) (hγ1 q) B W) :=
            seg_mono_le R hR hI B W hbounds hstrict (γ p) (γ q)
              (hγ0 p) (hγ1 p) (hγ0 q) (hγ1 q) hle
          exact hR.2 _ _ _ (hR.2 _ _ _ (hγspec p).1 hmid) (hγspec q).2.1
      refine ⟨fun x => γ (StdSimplex.single x), ?_⟩
      have hγeq : ∀ p, γ p
          = expectedUtility (fun x => γ (StdSimplex.single x)) p := by
        apply simplex_strong_induction
        · intro x
          simp only [expectedUtility_single]
        · intro x q α h0 h1 ih
          have haffx := haff (StdSimplex.single x) q α h0.le h1.le
          have heux := expectedUtility_mix (fun x => γ (StdSimplex.single x)) α
            h0.le h1.le (StdSimplex.single x) q
          have hu : ∀ y, (fun x => γ (StdSimplex.single x)) y
              = γ (StdSimplex.single y) := fun y => rfl
          rw [haffx, heux, expectedUtility_single, ih, ← hu]
      intro p q
      rw [hγrep p q, hγeq p, hγeq q]

end MathlibExt.Economics.ExpectedUtility
