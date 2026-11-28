/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.Additive.RepresentationCount
public import MathlibExt.Combinatorics.Additive.Sidon
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Sidon subsets of sets with bounded representation counts

For each `k ≥ 1`, every nonempty finite set `A ⊆ ℕ` with at most `k` ordered representations of
each sum has a Sidon subset of size at least `|A|^(2/3) / (8 * k)`. In particular, for each real
`C`, if `A` is sufficiently large in terms of `k` and `C`, it has a Sidon subset of size at least
`C * √|A|`. We use Alon and Erdős's sampling and deletion argument for inequality (4). Their `B₂`
condition tests sums of distinct terms; to obtain `Set.IsSidon` we also remove three-element
supports of collisions with a repeated summand, using the count in the proof of Theorem 3.

## References

* Noga Alon and P. Erdős, *An Application of Graph Theory to Additive Number Theory*, European
  Journal of Combinatorics 6 (1985), 201–203, Theorem 1 (inequality (4)) and the proof of Theorem 3.
* T. F. Bloom, [Erdős Problems, Problem #772](https://www.erdosproblems.com/772), first question.

The restriction of the uniform average to the colors on an edge follows the product splitting
in `mass_split` and `mass_restrict` in
`MathlibExt.Combinatorics.ThreeChromaticHypergraphDegreeErdosProblem833`.
-/

open Finset Filter
open scoped BigOperators

namespace MathlibExt.NumberTheory.SidonSubsetBoundedRepresentationsErdosProblem772Wanted

open AdditiveCombinatorics

/-- Erdős Problem 772, first question: for every `k ≥ 1`, `H_k(n) / √n → ∞`, where
`‖1_A ∗ 1_A‖_∞ ≤ k` bounds `AdditiveCombinatorics.orderedRepresentationCount` (ordered pairs). -/
@[expose] public def sidonSubsetBeyondSqrt : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ, A.card = n →
    (∀ m, AdditiveCombinatorics.orderedRepresentationCount (A : Set ℕ) m ≤ k) →
      ∃ S ⊆ A, (S : Set ℕ).IsSidon ∧ C * Real.sqrt n ≤ S.card

private def repPairs (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (antidiagonal m).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)

private lemma mem_repPairs {A : Finset ℕ} {m a b : ℕ} :
    (a, b) ∈ repPairs A m ↔ a + b = m ∧ a ∈ A ∧ b ∈ A := by
  simp [repPairs, mem_antidiagonal]

private lemma card_repPairs_le {A : Finset ℕ} {k : ℕ}
    (hk : ∀ m, orderedRepresentationCount (A : Set ℕ) m ≤ k) (m : ℕ) :
    (repPairs A m).card ≤ k := by
  simpa only [repPairs, ← orderedRepresentationCount_coe_finset A m] using hk m

private def collisionSupports {ι : Type*} (A : Finset ℕ) (I : Finset ι) (m : ι → ℕ)
    (support : ι → ℕ × ℕ → Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  (I.biUnion (fun i => (repPairs A (m i)).image (support i))).filter
    (fun e => e ⊆ A ∧ e.card = r)

private lemma card_collisionSupports_le {ι : Type*} {A : Finset ℕ} {k : ℕ}
    (hk : ∀ m, orderedRepresentationCount (A : Set ℕ) m ≤ k) (I : Finset ι) (m : ι → ℕ)
    (support : ι → ℕ × ℕ → Finset ℕ) (r : ℕ) :
    (collisionSupports A I m support r).card ≤ I.card * k := by
  calc
    _ ≤ (I.biUnion (fun i => (repPairs A (m i)).image (support i))).card := card_filter_le _ _
    _ ≤ ∑ i ∈ I, ((repPairs A (m i)).image (support i)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ I, k := sum_le_sum (fun i _ => card_image_le.trans (card_repPairs_le hk (m i)))
    _ = _ := by simp

private def sample {α : Type*} [DecidableEq α] (A : Finset α) {d : ℕ}
    (ω : A → Fin (d + 1)) : Finset α :=
  (univ.filter (fun a : A => ω a = 0)).map (Function.Embedding.subtype _)

private lemma mem_sample {α : Type*} [DecidableEq α] {A : Finset α} {d : ℕ}
    {ω : A → Fin (d + 1)} {a : α} : a ∈ sample A ω ↔ ∃ ha : a ∈ A, ω ⟨a, ha⟩ = 0 := by
  constructor
  · intro h
    obtain ⟨⟨b, hb⟩, hb₀, rfl⟩ := mem_map.mp h
    exact ⟨hb, (mem_filter.mp hb₀).2⟩
  · rintro ⟨ha, ha₀⟩
    exact mem_map.mpr ⟨⟨a, ha⟩, mem_filter.mpr ⟨mem_univ _, ha₀⟩, rfl⟩

-- Only the colors on `e` matter. Splitting the function at `e` leaves a singleton event
-- on the first factor and an unrestricted choice on the second factor.
private lemma expect_subset_sample {α : Type*} [DecidableEq α] {A e : Finset α}
    (he : e ⊆ A) (d : ℕ) :
    (𝔼 ω : A → Fin (d + 1), if e ⊆ sample A ω then (1 : ℝ) else 0) =
      1 / ((d : ℝ) + 1) ^ e.card := by
  classical
  let t := e.subtype (· ∈ A)
  let split := Equiv.piEquivPiSubtypeProd (· ∈ t) (fun _ => Fin (d + 1))
  have hcard : t.card = e.card := by
    rw [card_subtype, filter_eq_self.mpr he]
  have hrestrict (ω : A → Fin (d + 1)) : e ⊆ sample A ω ↔ (split ω).1 = 0 := by
    constructor
    · intro h
      funext i
      exact (mem_sample.mp (h (mem_subtype.mp i.2))).choose_spec
    · intro h a ha
      exact mem_sample.mpr ⟨he ha, congrFun h ⟨⟨a, he ha⟩, mem_subtype.mpr ha⟩⟩
  calc
    _ = 𝔼 p, if p.1 = (0 : t → Fin (d + 1)) then (1 : ℝ) else 0 :=
      Fintype.expect_equiv split _ _ (by intro ω; simp only [hrestrict])
    _ = 𝔼 f : t → Fin (d + 1), if f = 0 then (1 : ℝ) else 0 := by
      rw [← univ_product_univ, Finset.expect_product]
      refine expect_congr rfl (fun f _ => ?_)
      exact Fintype.expect_const (ι := {a : A // a ∉ t} → Fin (d + 1))
        (if f = 0 then (1 : ℝ) else 0)
    _ = _ := by
      rw [Fintype.expect_ite_eq']
      simp [hcard, NNRat.smul_def, div_eq_inv_mul]

private lemma expect_filter_card {Ω ι : Type*} [Fintype Ω] (E : Finset ι)
    (P : Ω → ι → Prop) [DecidableRel P] :
    (𝔼 ω, ((E.filter (P ω)).card : ℝ)) = ∑ i ∈ E, 𝔼 ω, if P ω i then (1 : ℝ) else 0 := by
  rw [← expect_sum_comm]
  apply expect_congr rfl
  intro ω _
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro i _
  split_ifs <;> norm_num

private lemma expect_surviving {α : Type*} [DecidableEq α] {A : Finset α}
    (E : Finset (Finset α)) (r d : ℕ) (hE : ∀ e ∈ E, e ⊆ A ∧ e.card = r) :
    (𝔼 ω : A → Fin (d + 1), ((E.filter (· ⊆ sample A ω)).card : ℝ)) =
      (E.card : ℝ) / ((d : ℝ) + 1) ^ r := by
  rw [expect_filter_card E (fun ω e => e ⊆ sample A ω)]
  calc
    _ = ∑ _ ∈ E, (1 : ℝ) / ((d : ℝ) + 1) ^ r := by
      apply sum_congr rfl
      intro e he
      rw [expect_subset_sample (hE e he).1, (hE e he).2]
    _ = _ := by simp [div_eq_mul_inv]

private lemma expect_sample_card {α : Type*} [DecidableEq α] (A : Finset α) (d : ℕ) :
    (𝔼 ω : A → Fin (d + 1), ((sample A ω).card : ℝ)) = (A.card : ℝ) / ((d : ℝ) + 1) := by
  have hω (ω : A → Fin (d + 1)) : A.filter (· ∈ sample A ω) = sample A ω := by
    ext a
    exact mem_filter.trans (and_iff_right_of_imp fun h => (mem_sample.mp h).choose)
  calc
    _ = ∑ a ∈ A, 𝔼 ω : A → Fin (d + 1), if a ∈ sample A ω then (1 : ℝ) else 0 := by
      rw [← expect_filter_card A (fun ω a => a ∈ sample A ω)]
      simp only [hω]
    _ = ∑ _ ∈ A, (1 : ℝ) / ((d : ℝ) + 1) := by
      apply sum_congr rfl
      intro a ha
      simp only [← singleton_subset_iff, expect_subset_sample (singleton_subset_iff.mpr ha),
        card_singleton, pow_one]
    _ = _ := by simp [div_eq_mul_inv]

private lemma exists_avoiding_supports {α : Type*} [DecidableEq α]
    (A : Finset α) (E₃ E₄ : Finset (Finset α)) (d : ℕ)
    (h₃ : ∀ e ∈ E₃, e ⊆ A ∧ e.card = 3) (h₄ : ∀ e ∈ E₄, e ⊆ A ∧ e.card = 4) :
    ∃ S ⊆ A, (∀ e ∈ E₃ ∪ E₄, ¬ e ⊆ S) ∧
      (A.card : ℝ) / (d + 1) - (E₃.card : ℝ) / (d + 1) ^ 3 -
        (E₄.card : ℝ) / (d + 1) ^ 4 ≤ S.card := by
  classical
  let score (ω : A → Fin (d + 1)) : ℝ :=
    (sample A ω).card - (E₃.filter (· ⊆ sample A ω)).card - (E₄.filter (· ⊆ sample A ω)).card
  have havg : (𝔼 ω, score ω) = (A.card : ℝ) / (d + 1) - (E₃.card : ℝ) / (d + 1) ^ 3 -
      (E₄.card : ℝ) / (d + 1) ^ 4 := by
    simp only [score, expect_sub_distrib, expect_sample_card, expect_surviving E₃ 3 d h₃,
      expect_surviving E₄ 4 d h₄]
  obtain ⟨ω, -, hω⟩ := exists_le_of_le_expect univ_nonempty havg.ge
  let U := sample A ω
  let E := (E₃ ∪ E₄).filter (· ⊆ U)
  have hnonempty (e : E) : e.val.Nonempty := by
    rcases mem_union.mp (mem_filter.mp e.2).1 with h | h
    · exact card_pos.mp (by rw [(h₃ _ h).2]; decide)
    · exact card_pos.mp (by rw [(h₄ _ h).2]; decide)
  let D := E.attach.image (fun e => (hnonempty e).choose)
  refine ⟨U \ D, sdiff_subset.trans (fun _ h => (mem_sample.mp h).choose), ?_, ?_⟩
  · intro e he hes
    have heE : e ∈ E := mem_filter.mpr ⟨he, hes.trans sdiff_subset⟩
    have hv := (hnonempty ⟨e, heE⟩).choose_spec
    exact (mem_sdiff.mp (hes hv)).2 (mem_image.mpr ⟨⟨e, heE⟩, mem_attach _ _, rfl⟩)
  · have hD : D.card ≤ E.card := card_image_le.trans_eq card_attach
    have hE : E.card ≤ (E₃.filter (· ⊆ U)).card + (E₄.filter (· ⊆ U)).card := by
      simpa only [E, filter_union] using
        card_union_le (s := E₃.filter (· ⊆ U)) (t := E₄.filter (· ⊆ U))
    have hU : U.card ≤ (U \ D).card + D.card := card_le_card_sdiff_add_card
    have hscore : score ω ≤ ((U \ D).card : ℝ) := by
      change (U.card : ℝ) - (E₃.filter (· ⊆ U)).card - (E₄.filter (· ⊆ U)).card ≤ _
      linarith [show (U.card : ℝ) ≤ (U \ D).card + D.card by exact_mod_cast hU,
        show (D.card : ℝ) ≤ (E₃.filter (· ⊆ U)).card + (E₄.filter (· ⊆ U)).card by
          exact_mod_cast hD.trans hE]
    exact hω.trans hscore

private lemma exists_sidon_of_representation_bound {A : Finset ℕ} {k : ℕ}
    (hk : ∀ m, orderedRepresentationCount (A : Set ℕ) m ≤ k) (d : ℕ) :
    ∃ S ⊆ A, (S : Set ℕ).IsSidon ∧
      (A.card : ℝ) / (d + 1) - (k : ℝ) * A.card / (d + 1) ^ 3 -
        (k : ℝ) * A.card ^ 2 / (d + 1) ^ 4 ≤ S.card := by
  let triple (a : ℕ) (p : ℕ × ℕ) : Finset ℕ := {a, p.1, p.2}
  let quad (q p : ℕ × ℕ) : Finset ℕ := {q.1, q.2, p.1, p.2}
  let E₃ := collisionSupports A A (fun a => a + a) triple 3
  let E₄ := collisionSupports A (A ×ˢ A) (fun q => q.1 + q.2) quad 4
  obtain ⟨S, hSA, havoids, hsize⟩ := exists_avoiding_supports A E₃ E₄ d
    (fun _ he => (mem_filter.mp he).2) (fun _ he => (mem_filter.mp he).2)
  refine ⟨S, hSA, ?_, ?_⟩
  · intro a ha b hb c hc v hv hsum
    by_contra h
    -- If the two sides shared any entry, cancellation would make the collision trivial.
    have hac : a ≠ c := fun e => h (Or.inl ⟨e, by omega⟩)
    have hav : a ≠ v := fun e => h (Or.inr ⟨e, by omega⟩)
    have hbc : b ≠ c := fun e => h (Or.inr ⟨by omega, e⟩)
    have hbv : b ≠ v := fun e => h (Or.inl ⟨by omega, e⟩)
    have htriple {x y z : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
        (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (heq : y + z = x + x) : False := by
      have hm : triple x (y, z) ∈ E₃ := by
        refine mem_filter.mpr ⟨mem_biUnion.mpr ⟨x, hSA hx,
          mem_image.mpr ⟨(y, z), mem_repPairs.mpr ⟨heq, hSA hy, hSA hz⟩, rfl⟩⟩,
          insert_subset (hSA hx) (insert_subset (hSA hy) (singleton_subset_iff.mpr (hSA hz))), ?_⟩
        simp [triple, card_insert_of_notMem, hxy, hxz, hyz]
      exact havoids _ (mem_union_left _ hm)
        (insert_subset hx (insert_subset hy (singleton_subset_iff.mpr hz)))
    by_cases hab : a = b
    · exact htriple ha hc hv hac hav (by omega) (by omega)
    by_cases hcv : c = v
    · exact htriple hc ha hb hac.symm hbc.symm hab (by omega)
    have hsub : quad (a, b) (c, v) ⊆ S :=
      insert_subset ha (insert_subset hb (insert_subset hc (singleton_subset_iff.mpr hv)))
    have hm : quad (a, b) (c, v) ∈ E₄ := by
      refine mem_filter.mpr ⟨mem_biUnion.mpr ⟨(a, b), mem_product.mpr ⟨hSA ha, hSA hb⟩,
        mem_image.mpr ⟨(c, v), mem_repPairs.mpr ⟨hsum.symm, hSA hc, hSA hv⟩, rfl⟩⟩,
        hsub.trans hSA, ?_⟩
      simp [quad, card_insert_of_notMem, hab, hac, hav, hbc, hbv, hcv]
    exact havoids _ (mem_union_right _ hm) hsub
  · have hE₃ : E₃.card ≤ A.card * k := card_collisionSupports_le hk _ _ _ _
    have hE₄ : E₄.card ≤ A.card ^ 2 * k := by
      simpa only [E₄, card_product, pow_two] using card_collisionSupports_le hk (A ×ˢ A)
        (fun q => q.1 + q.2) quad 4
    apply le_trans _ hsize
    gcongr
    · rw [mul_comm]; exact_mod_cast hE₃
    · rw [mul_comm]; exact_mod_cast hE₄

/-- **Quantitative Sidon subset bound.** If `k ≥ 1` and `A` is a nonempty finite set of
natural numbers with at most `k` ordered representations of each sum, then `A` contains a
Sidon subset of size at least `|A|^(2/3) / (8 * k)`. This is the sampling bound of Alon and Erdős
(inequality (4)), with repeated summands included in the Sidon condition. -/
public theorem exists_sidon_card_rpow {A : Finset ℕ} {k : ℕ} (hk : 1 ≤ k) (hA : 1 ≤ A.card)
    (hrep : ∀ m, orderedRepresentationCount (A : Set ℕ) m ≤ k) :
    ∃ S ⊆ A, (S : Set ℕ).IsSidon ∧ (A.card : ℝ) ^ ((2 : ℝ) / 3) / (8 * k) ≤ S.card := by
  let n : ℝ := A.card
  let x := n ^ ((1 : ℝ) / 3)
  let q : ℕ := 2 * k * ⌈x⌉₊
  have hn : 1 ≤ n := by
    change (1 : ℝ) ≤ (A.card : ℝ)
    exact_mod_cast hA
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : 1 ≤ x := Real.one_le_rpow hn (by norm_num)
  have hcube : x ^ 3 = n := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hq : (2 : ℝ) * k * x ≤ q := by
    push_cast [q]
    gcongr
    exact Nat.le_ceil x
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq
  have hq₀ : 0 < q := by exact_mod_cast hqpos
  have hqle : (q : ℝ) ≤ 4 * k * x := by
    have hceil : (⌈x⌉₊ : ℝ) ≤ 2 * x := by linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ x)]
    push_cast [q]
    calc
      _ ≤ 2 * (k : ℝ) * (2 * x) := by gcongr
      _ = _ := by ring
  have h2k : (2 : ℝ) * k ≤ q := (le_mul_of_one_le_right (by positivity) hx).trans hq
  have h4k : (4 : ℝ) * k ≤ (2 * (k : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) by positivity) (sub_nonneg.mpr hk')]
  have hsq : (4 : ℝ) * k ≤ (q : ℝ) ^ 2 := h4k.trans (by gcongr)
  have hcu : (4 : ℝ) * k * n ≤ (q : ℝ) ^ 3 := calc
    _ ≤ (2 * (k : ℝ)) ^ 2 * n := by gcongr
    _ ≤ (2 * (k : ℝ)) ^ 3 * n := by
      apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hn)
      rw [pow_succ (2 * (k : ℝ)) 2]
      exact le_mul_of_one_le_right (by positivity) (by linarith)
    _ = ((2 : ℝ) * k * x) ^ 3 := by rw [← hcube, mul_pow (2 * (k : ℝ)) x]
    _ ≤ _ := by gcongr
  obtain ⟨S, hs, hsid, hsize⟩ := exists_sidon_of_representation_bound hrep (q - 1)
  rw [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one, sub_add_cancel] at hsize
  change n / q - (k : ℝ) * n / (q : ℝ) ^ 3 - (k : ℝ) * n ^ 2 / (q : ℝ) ^ 4 ≤ S.card at hsize
  have h3 : (k : ℝ) * n / (q : ℝ) ^ 3 ≤ n / (4 * q) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      _ = 4 * (k : ℝ) * (n * q) := by ring
      _ ≤ (q : ℝ) ^ 2 * (n * q) := by gcongr
      _ = _ := by ring
  have h4 : (k : ℝ) * n ^ 2 / (q : ℝ) ^ 4 ≤ n / (4 * q) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      _ = (4 * (k : ℝ) * n) * (n * q) := by ring
      _ ≤ (q : ℝ) ^ 3 * (n * q) := by gcongr
      _ = _ := by ring
  have htwice : n / (4 * q) + n / (4 * q) = n / (2 * q) := by ring
  have hhalf : n / q - n / (2 * q) = n / (2 * q) := by ring
  refine ⟨S, hs, hsid, le_trans ?_ (show n / (2 * q) ≤ S.card by linarith)⟩
  have hpow : n ^ ((2 : ℝ) / 3) * x = n := by
    rw [show x = n ^ ((1 : ℝ) / 3) from rfl, ← Real.rpow_add (by positivity)]
    norm_num
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    _ ≤ n ^ ((2 : ℝ) / 3) * (2 * (4 * (k : ℝ) * x)) := by gcongr
    _ = _ := by calc
      _ = (n ^ ((2 : ℝ) / 3) * x) * (8 * (k : ℝ)) := by ring
      _ = _ := by rw [hpow]

/--
Resolved true: the sampling argument of Alon and Erdős gives `H_k(n) ≫_k n^{2/3}`, so
`H_k(n) / √n → ∞`; erdosproblems.com/772 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #772, https://www.erdosproblems.com/772 (status PROVED); resolution:
Noga Alon and P. Erdős, *An Application of Graph Theory to Additive Number Theory*, European
Journal of Combinatorics 6 (1985), 201–203, Theorem 1 (inequality (4)). Their `B₂` sequences
consider only sums of distinct terms. The same sampling argument gives the stated Sidon
convention, by also discarding supports of collisions `a + a = b + c` with three distinct terms.
-/
public theorem sidonSubsetBeyondSqrt_holds : sidonSubsetBeyondSqrt := by
  intro k hk C
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    ht.eventually (eventually_ge_atTop (8 * (k : ℝ) * C))] with n hn hC A hA hrep
  obtain ⟨S, hS, hsid, hsize⟩ := exists_sidon_card_rpow hk (hA ▸ hn) hrep
  refine ⟨S, hS, hsid, le_trans ?_ hsize⟩
  rw [hA, le_div_iff₀ (by positivity), Real.sqrt_eq_rpow,
    show (2 : ℝ) / 3 = 1 / 6 + 1 / 2 by norm_num, Real.rpow_add (by positivity)]
  calc
    _ = (8 * (k : ℝ) * C) * (n : ℝ) ^ ((1 : ℝ) / 2) := by ring
    _ ≤ _ := by gcongr

end MathlibExt.NumberTheory.SidonSubsetBoundedRepresentationsErdosProblem772Wanted
