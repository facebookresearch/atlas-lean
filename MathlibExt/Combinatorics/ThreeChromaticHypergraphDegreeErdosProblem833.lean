/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import MathlibExt.Combinatorics.HypergraphColoringShared
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.Probability.Combinatorics.LovaszLocalLemma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# High-degree vertices in three-chromatic hypergraphs

The symmetric Lovász local lemma gives an exponential lower bound on the largest vertex degree
of a uniform hypergraph that admits no proper two-coloring. We take `c = 1 / 16` in Erdős
Problem 833. For `r ≤ 8`, it suffices that some two edges meet. For larger `r`, independently
color each vertex with one of two colors and avoid all monochromatic edges.

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/ThreeChromaticHypergraphDegreeErdosProblem833Wanted.lean`:

Source: T. F. Bloom, Erdős Problems, Problem #833, https://www.erdosproblems.com/833 (status
PROVED). UnsolvedMath record UM-30007053 (`EP-833`), dataset ulamai/UnsolvedMath v1.8.0.

Hypergraphs are finite (on `Fin n`; by compactness this loses nothing); chromatic number `3` is
`3`-colorable and not `2`-colorable. The open-ended 'determine `f(r)`' on the page is not
formalized. Compared with the formal-conjectures statement `ErdosProblems/833.lean` (equivalent; no
code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ThreeChromaticHypergraphDegreeErdosProblem833Wanted

open MathlibExt.Combinatorics.HypergraphColoringShared

/-- **Erdős Problem 833.** The statement that there is a real $c > 0$ such that for every natural
number $r \ge 2$, every $n$ and every hypergraph $H$ on the vertex set $\{0, \dots, n-1\}$ (a
finite set of edges, each a set of exactly $r$ vertices) that is $3$-colorable but not
$2$-colorable, some vertex lies in at least $(1 + c)^r$ edges of $H$. -/
def threeChromaticHighDegreeVertex : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
    (∀ e ∈ H, e.card = r) → HypergraphColorable H 3 → ¬ HypergraphColorable H 2 →
      ∃ v : Fin n, (1 + c) ^ r ≤ ((H.filter fun e => v ∈ e).card : ℝ)

open Finset
open scoped BigOperators
open MathlibExt.Probability.Combinatorics.LovaszLocalLemma

private noncomputable def mass {α : Type*} [Fintype α] (P : α → Prop) : ℝ := by
  classical exact 𝔼 x, if P x then 1 else 0

private lemma mass_eq_sum {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    mass P = ∑ x, if P x then (Fintype.card α : ℝ)⁻¹ else 0 := by
  classical
  simp only [mass, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, sum_mul]
  congr 1
  funext x
  split_ifs <;> simp

-- Splitting the bits on and off an edge makes events on the two parts independent.
private lemma mass_split {n : ℕ} (e : Finset (Fin n)) (P : (e → Fin 2) → Prop)
    (Q : ({v // v ∉ e} → Fin 2) → Prop) :
    mass (fun ω : Fin n → Fin 2 => P (fun v => ω v) ∧ Q (fun v => ω v)) =
      mass P * mass Q := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (· ∈ e) (fun _ => Fin 2)
  unfold mass
  rw [Fintype.expect_mul_expect]
  refine (Fintype.expect_equiv split _ (fun p =>
    (if P p.1 then 1 else 0) * (if Q p.2 then 1 else 0)) ?_).trans ?_
  · intro ω
    by_cases hp : P (fun v => ω v) <;> by_cases hq : Q (fun v => ω v) <;>
      simp [split, hp, hq]
  · exact Finset.expect_product _ _ _

private lemma mass_restrict {n : ℕ} (e : Finset (Fin n)) (P : (e → Fin 2) → Prop) :
    mass (fun ω : Fin n → Fin 2 => P (fun v => ω v)) = mass P := by
  have h := mass_split e P (fun _ => True)
  simp only [and_true] at h
  simpa [mass, Fintype.expect_const] using h

private lemma mass_restrict_compl {n : ℕ} (e : Finset (Fin n))
    (Q : ({v // v ∉ e} → Fin 2) → Prop) :
    mass (fun ω : Fin n → Fin 2 => Q (fun v => ω v)) = mass Q := by
  have h := mass_split e (fun _ => True) Q
  simp only [true_and] at h
  simpa [mass, Fintype.expect_const] using h

private def constantOn {α : Type*} (x : α → Fin 2) : Prop := ∃ a, x = fun _ => a

private lemma mass_constantOn {n : ℕ} (e : Finset (Fin n)) :
    mass (constantOn (α := e)) ≤ 2 / (2 : ℝ) ^ e.card := by
  classical
  let colors := (univ : Finset (Fin 2)).image (fun a (_ : e) => a)
  have hmem (x : e → Fin 2) : constantOn x ↔ x ∈ colors := by
    simp [colors, constantOn, eq_comm]
  rw [mass_eq_sum]
  simp only [hmem, ← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
  have hc : colors.card ≤ 2 := card_image_le.trans_eq (by simp)
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
    (show (colors.card : ℝ) ≤ 2 by exact_mod_cast hc)
    (show 0 ≤ (Fintype.card (e → Fin 2) : ℝ)⁻¹ by positivity)

private def bad {n : ℕ} (e : Finset (Fin n)) (ω : Fin n → Fin 2) : Prop :=
  constantOn (fun v : e => ω v)

private def intersectionGraph {n : ℕ} (H : Finset (Finset (Fin n))) : SimpleGraph H where
  Adj e f := e ≠ f ∧ ¬ Disjoint e.val f.val
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

-- The other edges in a non-neighbor family only examine bits outside the given edge.
private lemma independent_bad {n : ℕ} {H : Finset (Finset (Fin n))} (e : H) (S : Finset H)
    (hS : ∀ f ∈ S, f ∉ insert e ((intersectionGraph H).neighborSet e)) :
    mass (fun ω => bad e.val ω ∧ ∀ f ∈ S, bad f.val ω) =
      mass (bad e.val) * mass (fun ω => ∀ f ∈ S, bad f.val ω) := by
  classical
  have hd (f : H) (hf : f ∈ S) : Disjoint e.val f.val := by
    by_contra hn
    exact hS f hf (Set.mem_insert_of_mem _ (show (intersectionGraph H).Adj e f from
      ⟨fun he => hS f hf (Set.mem_insert_iff.mpr (Or.inl he.symm)), hn⟩))
  let Q (y : {v // v ∉ e.val} → Fin 2) :=
    ∀ (f : H) (hf : f ∈ S), constantOn (fun v : f.val =>
      y ⟨v, fun hv => disjoint_left.mp (hd f hf) hv v.2⟩)
  change _ = mass (fun ω : Fin n → Fin 2 => constantOn (fun v : e.val => ω v)) *
    mass (fun ω : Fin n → Fin 2 => Q (fun v => ω v))
  rw [mass_restrict e.val, mass_restrict_compl e.val]
  exact mass_split e.val constantOn Q

open scoped Classical in
private lemma degree_bound {n r D : ℕ} (H : Finset (Finset (Fin n)))
    (hr : ∀ e ∈ H, e.card = r) (hD : ∀ v, (H.filter fun f => v ∈ f).card ≤ D) :
    ∀ e : H, (intersectionGraph H).degree e ≤ r * D := by
  classical
  intro e
  let star (v : Fin n) := H.filter (fun f => v ∈ f)
  have hsub : ((intersectionGraph H).neighborFinset e).image Subtype.val ⊆
      e.val.biUnion star := by
    intro f hf
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hf
    have hadj := ((intersectionGraph H).mem_neighborFinset e j).mp hj
    obtain ⟨v, he, hjv⟩ := not_disjoint_iff.mp hadj.2
    exact mem_biUnion.mpr ⟨v, he, mem_filter.mpr ⟨j.property, hjv⟩⟩
  calc
    (intersectionGraph H).degree e =
        (((intersectionGraph H).neighborFinset e).image Subtype.val).card :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (e.val.biUnion star).card := card_le_card hsub
    _ ≤ ∑ v ∈ e.val, (star v).card := card_biUnion_le
    _ ≤ ∑ _ ∈ e.val, D := sum_le_sum fun v _ => hD v
    _ = r * D := by simp [hr e.val e.property]

private lemma colorable_of_sparse {n r D : ℕ} (H : Finset (Finset (Fin n))) (hr₀ : 0 < r)
    (hr : ∀ e ∈ H, e.card = r) (hD : ∀ v, (H.filter fun f => v ∈ f).card ≤ D)
    (hsparse : Real.exp 1 * (2 / (2 : ℝ) ^ r) * (↑(r * D) + 1) ≤ 1) :
    HypergraphColorable H 2 := by
  classical
  let Ω := Fin n → Fin 2
  let A (e : H) : Set Ω := {ω | bad e.val ω}
  have hpos := lovasz_local_lemma_symmetric_finite
    (fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹) (fun _ => by positivity)
    (by simp [Fintype.card_ne_zero]) A (intersectionGraph H) (2 / (2 : ℝ) ^ r) (r * D)
    (by positivity)
    ((intersectionGraph H).maxDegree_le_of_forall_degree_le _ (degree_bound H hr hD))
    (fun e => ?_) (fun e S hS => ?_) hsparse
  · obtain ⟨ω, _, hω⟩ := (sum_pos_iff_of_nonneg (fun _ _ => by positivity)).mp hpos
    have hg : ∀ e : H, ω ∉ A e := by
      by_contra h
      rw [ite_eq_right h] at hω
      exact lt_irrefl _ hω
    refine ⟨ω, fun e he => ?_⟩
    by_contra! h
    obtain ⟨u, hu⟩ := card_pos.mp ((hr e he).symm ▸ hr₀)
    exact hg ⟨e, he⟩ ⟨ω u, funext fun v => h v v.2 u hu⟩
  · rw [← mass_eq_sum]
    change mass (fun ω : Fin n → Fin 2 => constantOn (fun v : e.val => ω v)) ≤ _
    rw [mass_restrict e.val, ← hr e.val e.property]
    exact mass_constantOn e.val
  · rw [← mass_eq_sum, ← mass_eq_sum, ← mass_eq_sum]
    exact independent_bad e S hS

-- For small uniformities, select one vertex per edge in a pairwise disjoint family.
private lemma colorable_of_degree_le_one {n r : ℕ} (H : Finset (Finset (Fin n))) (hr₂ : 2 ≤ r)
    (hr : ∀ e ∈ H, e.card = r) (hD : ∀ v, (H.filter fun f => v ∈ f).card ≤ 1) :
    HypergraphColorable H 2 := by
  classical
  have hpair (e : H) : ∃ u ∈ e.val, ∃ v ∈ e.val, u ≠ v :=
    one_lt_card.mp (by rw [hr e.val e.property]; omega)
  choose u hu v hv huv using hpair
  let c (x : Fin n) : Fin 2 := if x ∈ Set.range u then 0 else 1
  refine ⟨c, fun f hf => ?_⟩
  let e : H := ⟨f, hf⟩
  have hout : v e ∉ Set.range u := by
    rintro ⟨j, hj⟩
    have heq : j = e := Subtype.ext (card_le_one.mp (hD (v e)) j.val
      (mem_filter.mpr ⟨j.property, hj ▸ hu j⟩) e.val (mem_filter.mpr ⟨hf, hv e⟩))
    exact huv e (heq ▸ hj)
  refine ⟨u e, hu e, v e, hv e, ?_⟩
  simp only [c, ite_eq_left (Set.mem_range_self _), ite_eq_right hout]
  decide

private lemma exponential_margin {r : ℕ} (hr : 8 ≤ r) :
    6 * ((r : ℝ) + 1) * (17 / 16 : ℝ) ^ r ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    push_cast
    rw [pow_succ, pow_succ (2 : ℝ)]
    calc
      _ = (6 * ((r : ℝ) + 1 + 1) * (17 / 16)) * (17 / 16) ^ r := by ring
      _ ≤ (2 * (6 * ((r : ℝ) + 1))) * (17 / 16) ^ r := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [show (8 : ℝ) ≤ r by exact_mod_cast hr]
      _ = 6 * ((r : ℝ) + 1) * (17 / 16) ^ r * 2 := by ring
      _ ≤ _ := by gcongr

/--
**Erdős Problem 833 holds.** There is a real $c > 0$ such that for every natural number $r \ge 2$,
every $n$ and every hypergraph $H$ on the vertex set $\{0, \dots, n-1\}$ (a finite set of edges,
each a set of exactly $r$ vertices) that is $3$-colorable but not $2$-colorable, some vertex lies
in at least $(1 + c)^r$ edges of $H$.

Erdős and Lovász proved that every $r$-uniform hypergraph with chromatic number $3$ has a vertex
in at least $2^{r-1} / (4r)$ edges (Theorem 2 with $k = 2$), which exceeds $(1 + c)^r$ for a small
absolute $c$ once $r$ is large, while for every $r$ some vertex lies in two edges (pairwise
disjoint edges can be $2$-colored).

Source: T. F. Bloom, Erdős Problems, Problem #833, https://www.erdosproblems.com/833 (status
PROVED); resolution: P. Erdős and L. Lovász, Problems and results on 3-chromatic hypergraphs and
some related questions, Infinite and finite sets (Colloq. Keszthely, 1973), Colloq. Math. Soc. János
Bolyai 10 (1975), 609-627, Theorem 2: a (k + 1)-chromatic r-uniform hypergraph has an edge meeting
at least k^{r-1}/4 other edges, so some vertex has degree at least k^{r-1}/(4r); for k = 2 this is
2^{r-1}/(4r), https://users.renyi.hu/~p_erdos/1975-34.pdf.
-/
public theorem threeChromaticHighDegreeVertex_holds : threeChromaticHighDegreeVertex := by
  classical
  refine ⟨1 / 16, by norm_num, fun r hr n H hunif _ h₂ => ?_⟩
  rw [show (1 + 1 / 16 : ℝ) = 17 / 16 by norm_num]
  by_contra! hdeg
  apply h₂
  by_cases hsmall : r ≤ 8
  · apply colorable_of_degree_le_one H hr hunif
    intro v
    have h := (hdeg v).trans_le (pow_le_pow_right₀ (by norm_num) hsmall)
    have : ((H.filter fun e => v ∈ e).card : ℝ) < 2 := h.trans_le (by norm_num)
    exact Nat.le_of_lt_succ (by exact_mod_cast this)
  · let B := (17 / 16 : ℝ) ^ r
    have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
    apply colorable_of_sparse (D := ⌊B⌋₊) H (by omega) hunif (fun v => Nat.le_floor (hdeg v).le)
    have hD : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (zero_le_one.trans hB)
    have hcount : ((r * ⌊B⌋₊ : ℕ) : ℝ) + 1 ≤ (r + 1 : ℝ) * B := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg (α := ℝ) r)]
    rw [mul_comm (Real.exp 1 * _), ← mul_assoc, mul_div_assoc',
      div_le_iff₀ (by positivity), one_mul]
    calc
      _ ≤ ((r : ℝ) + 1) * B * 3 * 2 := by
        gcongr
        exact Real.exp_one_lt_three.le
      _ = 6 * ((r : ℝ) + 1) * B := by ring
      _ ≤ _ := exponential_margin (by omega)

end MathlibExt.Combinatorics.ThreeChromaticHypergraphDegreeErdosProblem833Wanted
