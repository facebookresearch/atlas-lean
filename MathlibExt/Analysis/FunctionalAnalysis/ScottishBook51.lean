/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Denumerable
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uncountable orthogonal systems without square integrability

A binary branch has a nonzero common base coordinate and a signed coordinate at each prefix.
For two distinct branches, their first differing bit gives a negative product that cancels the
geometric sum over the shared prefixes and the base coordinate. On the interval, disjoint
dyadic cells of positive measure realize the coordinates as weighted indicators.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook51Wanted

/-- Retain the original local restricted-Lebesgue instance on `[0, 1]` so the
exposed definitions use the same measure as their wanted versions. -/
noncomputable local instance scottishBook51MeasureSpace :
    MeasureTheory.MeasureSpace ↥(Set.Icc (0 : ℝ) 1) :=
  MeasureTheory.Measure.Subtype.measureSpace

/-- **Countability of orthogonal systems of sequences.** This is the statement that every set $S$
of real sequences $(f_n)_{n \in \mathbb{N}}$ with the following two properties is at most
countable: no member of $S$ is the zero sequence; and for any two distinct $f, g \in S$ the series
$\sum_{n} f_n g_n$ converges absolutely and its sum is $0$.

The zero sequence is excluded because it is orthogonal to everything, so without this it
would be a trivial member of every family. -/
def SequenceSystemsAreCountable : Prop :=
  ∀ S : Set (ℕ → ℝ),
    (∀ f ∈ S, f ≠ 0) →
    (∀ f ∈ S, ∀ g ∈ S, f ≠ g →
      Summable (fun n => f n * g n) ∧ ∑' n, f n * g n = 0) →
    S.Countable

/-- **Countability of orthogonal systems of functions.** Let $\lambda$ be Lebesgue measure on
$[0, 1]$. This is the statement that every set $S$ of functions $[0, 1] \to \mathbb{R}$ with the
following three properties is at most countable: no member of $S$ is $\lambda$-almost everywhere
equal to $0$; any two members of $S$ that are equal $\lambda$-almost everywhere are equal; and
any two members $f, g$ of $S$ that are not equal $\lambda$-almost everywhere are measurable, have
$\lambda$-integrable product $fg$, and satisfy $\int_{[0, 1]} f g \, d\lambda = 0$.

No square-integrability is assumed. Without the second property, uncountably many
almost-everywhere-equal copies of one function would satisfy the orthogonality condition
vacuously. The first property excludes the indicator functions of single points, each of which
is zero almost everywhere. -/
def FunctionSystemsAreCountable : Prop :=
  ∀ S : Set (↥(Set.Icc (0 : ℝ) 1) → ℝ),
    (∀ f ∈ S, ¬ (f =ᵐ[MeasureTheory.volume] 0)) →
    (∀ f ∈ S, ∀ g ∈ S, f =ᵐ[MeasureTheory.volume] g → f = g) →
    (∀ f ∈ S, ∀ g ∈ S, ¬ (f =ᵐ[MeasureTheory.volume] g) →
      Measurable f ∧ Measurable g ∧
      MeasureTheory.Integrable (fun x : ↥(Set.Icc (0 : ℝ) 1) => f x * g x) ∧
      MeasureTheory.integral MeasureTheory.volume
        (fun x : ↥(Set.Icc (0 : ℝ) 1) => f x * g x) = 0) →
    S.Countable

/-! ### An uncountable family with finitely supported pairwise products -/

private abbrev Branch := ℕ → Bool
private abbrev Word := Σ n : ℕ, Fin n → Bool
private abbrev Coordinate := Option Word

private def branchPrefix (a : Branch) (n : ℕ) : Fin n → Bool := fun i => a i

private def coord (a : Branch) (n : ℕ) : Coordinate := some ⟨n, branchPrefix a n⟩

private theorem coord_injective (a : Branch) : Injective (coord a) := by
  intro n m h
  simpa only [coord, Option.map_some, Option.some.injEq] using
    congrArg (Option.map (fun w : Word => w.1)) h

private def signB : Bool → ℝ
  | false => 1
  | true => -1

private def value (a : Branch) : Coordinate → ℝ := by
  classical
  exact fun
    | none => 1
    | some ⟨n, w⟩ => if w = branchPrefix a n then signB (a n) * Real.sqrt (2 ^ n) else 0

private theorem same_sign_mul (c : Bool) (r : ℝ) :
    (signB c * r) * (signB c * r) = r ^ 2 := by
  cases c <;> simp [signB, pow_two]

private theorem opposite_sign_mul {c d : Bool} (h : c ≠ d) (r : ℝ) :
    (signB c * r) * (signB d * r) = -(r ^ 2) := by
  cases c <;> cases d <;> simp_all [signB, pow_two]

private theorem pair_finite_zero (a b : Branch) (hab : a ≠ b) :
    ∃ s : Finset Coordinate,
      (∀ q ∉ s, value a q * value b q = 0) ∧
      (∑ q ∈ s, value a q * value b q) = 0 := by
  classical
  have hdiff : ∃ n, a n ≠ b n := by
    by_contra! h
    exact hab (funext h)
  let k := Nat.find hdiff
  have hk : a k ≠ b k := Nat.find_spec hdiff
  have hlt (i : ℕ) (hi : i < k) : a i = b i := by
    by_contra h
    exact (not_lt_of_ge (Nat.find_min' hdiff h)) hi
  let u := (Finset.range (k + 1)).image (coord a)
  let s := insert none u
  refine ⟨s, ?_, ?_⟩
  · intro q hq
    cases q with
    | none => exact (hq (Finset.mem_insert_self ..)).elim
    | some q =>
      obtain ⟨n, w⟩ := q
      by_cases hA : w = branchPrefix a n
      · by_cases hB : w = branchPrefix b n
        · exfalso
          apply hq
          apply Finset.mem_insert_of_mem
          refine Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr ?_, ?_⟩
          · apply Nat.lt_succ_of_le
            by_contra hn
            have hi : k < n := by omega
            exact hk (congrFun (hA.symm.trans hB) ⟨k, hi⟩)
          · simp only [coord, hA]
        · simp only [value, ite_eq_right hB, mul_zero]
      · simp only [value, ite_eq_right hA, zero_mul]
  have hf (n : ℕ) (hn : n ≤ k) :
      value a (coord a n) * value b (coord a n) =
        if n = k then -(2 : ℝ) ^ n else (2 : ℝ) ^ n := by
    have hp : branchPrefix a n = branchPrefix b n :=
      funext fun i => hlt i (lt_of_lt_of_le i.isLt hn)
    simp only [coord, value, ite_eq_left hp, ite_true]
    have hsqrt : Real.sqrt ((2 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
    by_cases hnk : n = k
    · subst n
      rw [ite_eq_left rfl, opposite_sign_mul hk, hsqrt]
    · rw [ite_eq_right hnk, hlt n (lt_of_le_of_ne hn hnk), same_sign_mul, hsqrt]
  have hnone : none ∉ u := by simp [u, coord]
  change (∑ q ∈ insert none u, value a q * value b q) = 0
  rw [Finset.sum_insert hnone]
  simp only [value, one_mul]
  change (1 : ℝ) + (∑ q ∈ (Finset.range (k + 1)).image (coord a), value a q * value b q) = 0
  rw [Finset.sum_image (fun _ _ _ _ h => coord_injective a h), Finset.sum_range_succ]
  have hsum : (∑ n ∈ Finset.range k, value a (coord a n) * value b (coord a n)) =
      ∑ n ∈ Finset.range k, (2 : ℝ) ^ n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [hf n hn'.le, ite_eq_right hn'.ne]
  rw [hsum, hf k le_rfl, ite_eq_left rfl]
  have hgeom := geom_sum_mul_add (1 : ℝ) k
  norm_num at hgeom
  linarith

private def coordinateIndex : Coordinate ≃ ℕ := by
  letI : Infinite Word := Infinite.of_injective (fun n : ℕ => (⟨n, fun _ => false⟩ : Word))
    (fun _ _ h => congrArg (fun w : Word => w.1) h)
  letI : Denumerable Coordinate := Denumerable.ofEncodableOfInfinite Coordinate
  exact Denumerable.eqv Coordinate

private def seq (a : Branch) (n : ℕ) : ℝ := value a (coordinateIndex.symm n)

private theorem seq_base (a : Branch) : seq a (coordinateIndex none) = 1 := by
  simp only [seq, Equiv.symm_apply_apply, value]

private theorem seq_pair_finite_zero (a b : Branch) (hab : a ≠ b) :
    ∃ s : Finset ℕ, (∀ n ∉ s, seq a n * seq b n = 0) ∧
      (∑ n ∈ s, seq a n * seq b n) = 0 := by
  classical
  obtain ⟨t, ht, hSum⟩ := pair_finite_zero a b hab
  refine ⟨t.map coordinateIndex.toEmbedding, ?_, ?_⟩
  · intro n hn
    apply ht (coordinateIndex.symm n)
    intro hn'
    apply hn
    exact Finset.mem_map.mpr ⟨coordinateIndex.symm n, hn', coordinateIndex.apply_symm_apply n⟩
  · rw [Finset.sum_map]
    simpa only [Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding, seq, Equiv.symm_apply_apply]
      using hSum

private theorem seq_injective : Injective seq := by
  intro a b he
  by_contra hab
  obtain ⟨s, hs, hsum⟩ := seq_pair_finite_zero a b hab
  have hm : coordinateIndex none ∈ s := by
    by_contra hn
    simpa only [seq_base, one_mul, one_ne_zero] using hs _ hn
  have hle := Finset.single_le_sum (f := fun n => seq a n * seq b n)
    (fun n _ => by rw [← he]; exact mul_self_nonneg _) hm
  rw [hsum, seq_base, seq_base, one_mul] at hle
  norm_num at hle

private theorem branch_uncountable : Uncountable Branch := by
  rw [← not_countable_iff]
  intro h
  let _ : Countable Branch := h
  obtain ⟨f, hf⟩ := exists_surjective_nat Branch
  obtain ⟨n, hn⟩ := hf (fun i => !(f i i))
  have he := congrFun hn n
  cases hb : f n n <;> simp [hb] at he

/-! ### Realization on disjoint dyadic cells -/

private abbrev I := ↥(Icc (0 : ℝ) 1)

private def dyadic (n : ℕ) : ℝ := (1 / 2) ^ n

private theorem dyadic_pos (n : ℕ) : 0 < dyadic n := pow_pos (by norm_num) _

private theorem dyadic_anti : StrictAnti dyadic := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have h : 0 < (1 / 2 : ℝ) ^ n := dyadic_pos n
  simpa only [dyadic, pow_succ] using
    (show (1 / 2 : ℝ) ^ n * (1 / 2) < (1 / 2 : ℝ) ^ n by linarith)

private theorem dyadic_le_one (n : ℕ) : dyadic n ≤ 1 := by
  simpa only [dyadic, pow_zero] using dyadic_anti.antitone (Nat.zero_le n)

private def cell (n : ℕ) : Set I := Subtype.val ⁻¹' Ioc (dyadic (n + 1)) (dyadic n)

private theorem cell_measurable (n : ℕ) : MeasurableSet (cell n) :=
  measurableSet_Ioc.preimage measurable_subtype_coe

private theorem cell_disjoint {n m : ℕ} (h : n ≠ m) : Disjoint (cell n) (cell m) := by
  refine Set.disjoint_left.mpr fun t hn hm => ?_
  change dyadic (n + 1) < (t : ℝ) ∧ (t : ℝ) ≤ dyadic n at hn
  change dyadic (m + 1) < (t : ℝ) ∧ (t : ℝ) ≤ dyadic m at hm
  rcases lt_or_gt_of_ne h with hnm | hmn
  · exact hn.1.not_ge (hm.2.trans (dyadic_anti.antitone (Nat.succ_le_of_lt hnm)))
  · exact hm.1.not_ge (hn.2.trans (dyadic_anti.antitone (Nat.succ_le_of_lt hmn)))

private theorem cell_volume (n : ℕ) :
    (volume : Measure I) (cell n) = ENNReal.ofReal (dyadic n - dyadic (n + 1)) := by
  rw [unitInterval.volume_apply, ← Real.volume_Ioc]
  congr 1
  apply Set.Subset.antisymm
  · rintro t ⟨x, hx, rfl⟩
    exact hx
  · intro t ht
    refine ⟨⟨t, ⟨(dyadic_pos _).le.trans ht.1.le, ht.2.trans (dyadic_le_one n)⟩⟩, ht, rfl⟩

private theorem cell_volume_pos (n : ℕ) : 0 < (volume : Measure I) (cell n) := by
  rw [cell_volume, ENNReal.ofReal_pos]
  exact sub_pos.mpr (dyadic_anti (Nat.lt_succ_self n))

private theorem cell_volume_ne_top (n : ℕ) : (volume : Measure I) (cell n) ≠ ∞ := by
  rw [cell_volume]
  exact ENNReal.ofReal_ne_top

private theorem cell_real_pos (n : ℕ) : 0 < (volume : Measure I).real (cell n) :=
  ENNReal.toReal_pos (cell_volume_pos n).ne' (cell_volume_ne_top n)

private def liftFn (x : ℕ → ℝ) (t : I) : ℝ :=
  ∑' n : ℕ, (cell n).indicator (fun _ => x n / Real.sqrt ((volume : Measure I).real (cell n))) t

private theorem liftFn_measurable (x : ℕ → ℝ) : Measurable (liftFn x) :=
  Measurable.tsum fun n => measurable_const.indicator (cell_measurable n)

private theorem liftFn_on_cell (x : ℕ → ℝ) {t : I} {n : ℕ} (ht : t ∈ cell n) :
    liftFn x t = x n / Real.sqrt ((volume : Measure I).real (cell n)) := by
  unfold liftFn
  rw [tsum_eq_single n]
  · rw [Set.indicator_of_mem ht]
  · intro m hm
    exact Set.indicator_of_notMem
      (fun ht' => Set.disjoint_left.mp (cell_disjoint hm) ht' ht) _

private theorem liftFn_outside (x : ℕ → ℝ) {t : I} (ht : ∀ n, t ∉ cell n) : liftFn x t = 0 := by
  unfold liftFn
  calc
    _ = ∑' _ : ℕ, (0 : ℝ) := tsum_congr fun n => Set.indicator_of_notMem (ht n) _
    _ = 0 := tsum_zero

private theorem liftFn_ae_injective {x y : ℕ → ℝ} (h : liftFn x =ᵐ[volume] liftFn y) : x = y := by
  funext n
  let r := Real.sqrt ((volume : Measure I).real (cell n))
  have hr : r ≠ 0 := (Real.sqrt_pos_of_pos (cell_real_pos n)).ne'
  have heq : x n / r = y n / r := by
    by_contra hne
    have hz : (volume : Measure I) {t | liftFn x t ≠ liftFn y t} = 0 := ae_iff.mp h
    have hs : cell n ⊆ {t | liftFn x t ≠ liftFn y t} := by
      intro t ht
      change liftFn x t ≠ liftFn y t
      rw [liftFn_on_cell x ht, liftFn_on_cell y ht]
      exact hne
    have hc := measure_mono (μ := (volume : Measure I)) hs
    rw [hz] at hc
    exact (cell_volume_pos n).not_ge hc
  exact mul_right_cancel₀ (inv_ne_zero hr) (by simpa only [div_eq_mul_inv] using heq)

private def productTerm (x y : ℕ → ℝ) (n : ℕ) : I → ℝ :=
  (cell n).indicator (fun _ => x n * y n / (volume : Measure I).real (cell n))

private theorem liftFn_mul_eq_sum {x y : ℕ → ℝ} {s : Finset ℕ}
    (hs : ∀ n ∉ s, x n * y n = 0) (t : I) :
    liftFn x t * liftFn y t = ∑ n ∈ s, productTerm x y n t := by
  classical
  by_cases ht : ∃ n, t ∈ cell n
  · obtain ⟨n, hn⟩ := ht
    rw [liftFn_on_cell x hn, liftFn_on_cell y hn, div_mul_div_comm, ← pow_two,
      Real.sq_sqrt (cell_real_pos n).le]
    have hoff (m : ℕ) (hm : m ≠ n) : productTerm x y m t = 0 :=
      Set.indicator_of_notMem (fun hm' => Set.disjoint_left.mp (cell_disjoint hm) hm' hn) _
    by_cases hmem : n ∈ s
    · rw [Finset.sum_eq_single n (fun m _ hm => hoff m hm) (fun h => (h hmem).elim)]
      rw [productTerm, Set.indicator_of_mem hn]
    · rw [Finset.sum_eq_zero (fun m hm => hoff m (fun h => hmem (h ▸ hm))), hs n hmem,
        zero_div]
  · have ht' (n : ℕ) : t ∉ cell n := fun h => ht ⟨n, h⟩
    rw [liftFn_outside x ht', zero_mul]
    exact (Finset.sum_eq_zero fun n _ => Set.indicator_of_notMem (ht' n) _).symm

private theorem liftFn_pair {x y : ℕ → ℝ} {s : Finset ℕ}
    (hs : ∀ n ∉ s, x n * y n = 0) :
    Integrable (fun t : I => liftFn x t * liftFn y t) ∧
      (∫ t : I, liftFn x t * liftFn y t) = ∑ n ∈ s, x n * y n := by
  have hEq : (fun t : I => liftFn x t * liftFn y t) = fun t => ∑ n ∈ s, productTerm x y n t :=
    funext (liftFn_mul_eq_sum hs)
  have hi (n : ℕ) : Integrable (productTerm x y n) :=
    (integrable_const _).indicator (cell_measurable n)
  rw [hEq]
  refine ⟨integrable_finsetSum s (fun n _ => hi n), ?_⟩
  rw [integral_finsetSum s (fun n _ => hi n)]
  apply Finset.sum_congr rfl
  intro n _
  rw [productTerm, integral_indicator_const _ (cell_measurable n), smul_eq_mul]
  field_simp [(cell_real_pos n).ne']

private theorem liftFn_zero : liftFn 0 = 0 := by
  funext t
  simp [liftFn]

private theorem seq_ne_zero (a : Branch) : seq a ≠ 0 := by
  intro h
  have hz := congrFun h (coordinateIndex none)
  simp only [seq_base, Pi.zero_apply, one_ne_zero] at hz

private theorem range_not_countable {α : Type*} {f : Branch → α} (hf : Injective f) :
    ¬ (Set.range f).Countable := by
  intro h
  let _ : Countable (Set.range f) := h.to_subtype
  let g (a : Branch) : Set.range f := ⟨f a, mem_range_self a⟩
  have hg : Injective g := fun _ _ h => hf (congrArg Subtype.val h)
  exact (not_countable_iff.mpr branch_uncountable) hg.countable

/--
**Orthogonal systems need not be countable.** Both of the following statements are false.
(a) Every set $S$ of real sequences $(f_n)_{n \in \mathbb{N}}$ in which no member is the zero
sequence, and in which for any two distinct $f, g \in S$ the series $\sum_n f_n g_n$ converges
absolutely with sum $0$, is at most countable. (b) Let $\lambda$ be Lebesgue measure on
$[0, 1]$. Every set $S$ of functions $[0, 1] \to \mathbb{R}$ in which no member is
$\lambda$-almost everywhere equal to $0$, no two distinct members are equal $\lambda$-almost
everywhere, and any two members $f, g$ that are not equal $\lambda$-almost everywhere are
measurable with $fg$ $\lambda$-integrable and $\int_{[0, 1]} f g \, d\lambda = 0$, is at most
countable.

This answers both parts of Mazur's Problem 51 of the Scottish Book in the negative: Plichko and
Razenkov construct a continuum-sized pairwise-orthogonal family of sequences, and from it an
uncountable orthogonal system of functions on an interval. No square-integrability is assumed;
in $\ell^2$ or $L^2$ an orthogonal family is at most countable, since those spaces are
separable Hilbert spaces.

Source: S. Mazur, Problem 51 of the Scottish Book; A. Plichko and A. Razenkov,
*On three problems from the Scottish Book connected with orthogonal systems*,
Colloq. Math. 70 (1996), 227–234, [Section 3](https://doi.org/10.4064/cm-70-2-227-234),
Proposition 4 and the paragraph after its proof; see the commentary in R. D. Mauldin (ed.),
*The Scottish Book*, 2nd ed. (Birkhäuser, 2015).
-/
theorem orthogonal_systems_not_necessarily_countable :
    ¬ SequenceSystemsAreCountable ∧ ¬ FunctionSystemsAreCountable := by
  constructor
  · intro h
    refine range_not_countable seq_injective (h (Set.range seq) ?_ ?_)
    · intro f hf
      obtain ⟨a, rfl⟩ := hf
      exact seq_ne_zero a
    · intro f hf g hg hfg
      obtain ⟨a, rfl⟩ := hf
      obtain ⟨b, rfl⟩ := hg
      obtain ⟨s, hs, hsum⟩ := seq_pair_finite_zero a b (fun h => hfg (congrArg seq h))
      exact ⟨summable_of_ne_finset_zero hs, (tsum_eq_sum hs).trans hsum⟩
  · intro h
    let f (a : Branch) := liftFn (seq a)
    have hf : Injective f := by
      intro a b heq
      exact seq_injective (liftFn_ae_injective (Filter.Eventually.of_forall (congrFun heq)))
    refine range_not_countable hf (h (Set.range f) ?_ ?_ ?_)
    · intro x hx hzero
      obtain ⟨a, rfl⟩ := hx
      change liftFn (seq a) =ᵐ[volume] (0 : I → ℝ) at hzero
      rw [← liftFn_zero] at hzero
      exact seq_ne_zero a (liftFn_ae_injective hzero)
    · intro x hx y hy heq
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact congrArg liftFn (liftFn_ae_injective heq)
    · intro x hx y hy hxy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      have hab : a ≠ b := by
        intro ha
        subst b
        exact hxy Filter.EventuallyEq.rfl
      obtain ⟨s, hs, hsum⟩ := seq_pair_finite_zero a b hab
      obtain ⟨hint, heq⟩ := liftFn_pair hs
      exact ⟨liftFn_measurable _, liftFn_measurable _, hint, heq.trans hsum⟩

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook51Wanted
