/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bubble sizes in linear chord diagrams

The theorem `MetaMathlibExt.mean_bubble_size` computes the mean by counting vertices
and starts of maximal intervals free of short chords. The theorem
`MetaMathlibExt.sum_mul_bubbleCount` gives the total size of these intervals over all diagrams.

Among the $D$ diagrams on $2n$ vertices, a prescribed chord occurs in $D/(2n-1)$ diagrams,
by symmetry of the possible partners. After fixing that chord, a remaining vertex has $2n-3$
possible partners. These two counts suffice because a bubble starts either at a free first vertex
or immediately after a short chord whose next vertex is free. Each diagram is a product of $n$
disjoint transpositions, giving $D = (2n)!/(2^n n!)$.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Linear chord diagrams.** A linear chord diagram on the $2n$ vertices $0, \dots, 2n-1$, laid
out on a line, is encoded by a map $\sigma$ from $\{0, \dots, 2n-1\}$ to itself that is a
fixed-point-free involution: $\sigma(i) \ne i$ and $\sigma(\sigma(i)) = i$ for every vertex $i$.
Vertex $i$ is joined by a chord to $\sigma(i)$.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (linear chord diagrams on `2n` vertices). -/
def IsLinearChordDiagram (n : ℕ) (σ : Fin (2 * n) → Fin (2 * n)) : Prop :=
  ∀ i, σ i ≠ i ∧ σ (σ i) = i

instance (n : ℕ) : DecidablePred (IsLinearChordDiagram n) := fun σ => by
  unfold IsLinearChordDiagram; infer_instance

/-- **Endpoints of short chords.** Let $\sigma$ be a map from $\{0, \dots, 2n-1\}$ to itself (for a
linear chord diagram, vertex $i$ is joined by a chord to $\sigma(i)$). A vertex $i$ is an
endpoint of a short chord of $\sigma$ when $\sigma(i) = i - 1$ or $\sigma(i) = i + 1$, that is,
when $i$ is joined to an adjacent vertex.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Abstract and Section 1 (short chords). -/
def IsShortChordVertex {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n)) : Prop :=
  (σ i : ℕ) + 1 = i ∨ (i : ℕ) + 1 = σ i

instance {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) : DecidablePred (IsShortChordVertex σ) :=
  fun i => by unfold IsShortChordVertex; infer_instance

/-- **Bubbles.** Let $\sigma$ be a map from $\{0, \dots, 2n-1\}$ to itself (for a linear chord
diagram, vertex $i$ is joined by a chord to $\sigma(i)$). For natural numbers $a$ and $p$, the
vertices $a, a+1, \dots, a+p-1$ form a bubble of size $p$ in $\sigma$ when $p \ge 1$,
$a + p \le 2n$, none of these vertices is an endpoint of a short chord of $\sigma$, the vertex
$a - 1$ is an endpoint of a short chord unless $a = 0$, and the vertex $a + p$ is an endpoint
of a short chord unless $a + p = 2n$.

So a bubble is a maximal run of consecutive vertices containing no endpoint of a short chord.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (definition of bubbles and their size). -/
def IsBubble {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (a p : ℕ) : Prop :=
  0 < p ∧ a + p ≤ 2 * n ∧
    (∀ i : Fin (2 * n), a ≤ (i : ℕ) → (i : ℕ) < a + p → ¬ IsShortChordVertex σ i) ∧
    (∀ i : Fin (2 * n), (i : ℕ) + 1 = a → IsShortChordVertex σ i) ∧
    (∀ i : Fin (2 * n), (i : ℕ) = a + p → IsShortChordVertex σ i)

instance {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (p : ℕ) :
    DecidablePred (fun a => IsBubble σ a p) := fun a => by
  unfold IsBubble; infer_instance

/-- **Bubble counts.** For natural numbers $n$ and $p$, $B_{n,p}$ is the total number of bubbles of
size $p$ in all linear chord diagrams on $2n$ vertices: the sum, over all linear chord diagrams
$\sigma$ on the vertices $0, \dots, 2n-1$, of the number of vertices $a$ such that the vertices
$a, a+1, \dots, a+p-1$ form a bubble of size $p$ in $\sigma$. In particular $B_{n,0} = 0$.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (definition of `B_{n,p}`, Table 1). -/
def bubbleCount (n p : ℕ) : ℕ :=
  ∑ σ ∈ Finset.univ.filter (IsLinearChordDiagram n),
    ((Finset.range (2 * n)).filter (fun a => IsBubble σ a p)).card

/-- **No bubbles of size one on two vertices.** $B_{1,1} = 0$: the linear chord diagrams on $2$
vertices have no bubble of size $1$. The only such diagram is a single short chord.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 1`). -/
theorem bubbleCount_one_one : bubbleCount 1 1 = 0 := by decide +kernel

/-- **Bubbles of size one on four vertices.** $B_{2,1} = 2$: the linear chord diagrams on $4$
vertices have $2$ bubbles of size $1$ in total.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 2`). -/
theorem bubbleCount_two_one : bubbleCount 2 1 = 2 := by decide +kernel

/-- **Bubbles of size four on four vertices.** $B_{2,4} = 1$: the linear chord diagrams on $4$
vertices have exactly one bubble of size $4$ in total. It consists of all four vertices of the
crossing diagram (chords $\{0, 2\}$ and $\{1, 3\}$), which has no short chord.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 2`). -/
theorem bubbleCount_two_four : bubbleCount 2 4 = 1 := by decide +kernel

namespace mean_bubble_size

open Finset

private abbrev DiagramMap (n : ℕ) := Fin (2 * n) → Fin (2 * n)

private def diagrams (n : ℕ) := univ.filter (IsLinearChordDiagram n)

private noncomputable abbrev bit (P : Prop) : ℚ := @ite _ P (Classical.propDecidable P) 1 0

private theorem sum_bit {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    ∑ x ∈ s, bit (P x) = (s.filter P).card := by
  rw [natCast_card_filter]
  apply sum_congr rfl
  intro x _
  by_cases h : P x <;> simp [bit, h]

-- Extend the predicate for a vertex free of short chords by false outside the diagram.
private def Free {n : ℕ} (σ : DiagramMap n) (i : ℕ) : Prop :=
  ∃ h : i < 2 * n, ¬IsShortChordVertex σ ⟨i, h⟩

private theorem bubble_iff {n a p : ℕ} {σ : DiagramMap n} :
    IsBubble σ a p ↔ 0 < p ∧ a + p ≤ 2 * n ∧
      (∀ i, a ≤ i → i < a + p → Free σ i) ∧
      (a = 0 ∨ ¬Free σ (a - 1)) ∧ ¬Free σ (a + p) := by
  unfold IsBubble Free
  constructor
  · rintro ⟨hp, hle, h, hl, hr⟩
    refine ⟨hp, hle, fun i ha hi => ⟨by omega, h ⟨i, by omega⟩ ha hi⟩, ?_, ?_⟩
    · by_cases ha : a = 0
      · exact Or.inl ha
      · exact Or.inr fun ⟨hi, h'⟩ => h' (hl ⟨_, hi⟩ (by dsimp; omega))
    · exact fun ⟨hi, h'⟩ => h' (hr ⟨_, hi⟩ rfl)
  · rintro ⟨hp, hle, h, hl, hr⟩
    refine ⟨hp, hle, fun i ha hi => (h i ha hi).choose_spec, ?_, ?_⟩
    · rintro ⟨i, hi⟩ he
      dsimp at he
      obtain rfl : a = i + 1 := he.symm
      simp only [Nat.add_one_ne_zero, false_or, Nat.add_sub_cancel] at hl
      exact of_not_not fun hn => hl ⟨hi, hn⟩
    · rintro ⟨i, hi⟩ rfl
      exact of_not_not fun hn => hr ⟨hi, hn⟩

-- Every free vertex lies in a unique maximal free interval.
private theorem unique_bubble {n i : ℕ} {σ : DiagramMap n} (hi : Free σ i) :
    ∃ a p, (IsBubble σ a p ∧ a ≤ i ∧ i < a + p) ∧
      ∀ b q, IsBubble σ b q → b ≤ i → i < b + q → b = a ∧ q = p := by
  classical
  have hL : ∃ a : ℕ, ∀ j, a ≤ j → j ≤ i → Free σ j :=
    ⟨i, fun j hj hj' => le_antisymm hj hj' ▸ hi⟩
  have hi' := hi.choose
  have hend : ¬Free σ (2 * n) := fun h => (lt_irrefl _ h.choose)
  have hR : ∃ b : ℕ, i ≤ b ∧ ¬Free σ b := ⟨2 * n, by omega, hend⟩
  let a := Nat.find hL
  let b := Nat.find hR
  have ha : a ≤ i := Nat.find_min' hL (fun j hj hj' => le_antisymm hj hj' ▸ hi)
  have hb : i ≤ b ∧ ¬Free σ b := Nat.find_spec hR
  have hbi : i < b := by by_contra! h; exact hb.2 (le_antisymm h hb.1 ▸ hi)
  have hbm : b ≤ 2 * n := Nat.find_min' hR ⟨by omega, hend⟩
  have inside : ∀ j, a ≤ j → j < b → Free σ j := by
    intro j hj hj'
    by_cases hji : j ≤ i
    · exact Nat.find_spec hL j hj hji
    · by_contra hn
      exact Nat.find_min hR hj' ⟨by omega, hn⟩
  have leftEnd : a = 0 ∨ ¬Free σ (a - 1) := by
    by_cases hz : a = 0
    · exact Or.inl hz
    · refine Or.inr fun h => Nat.find_min hL (m := a - 1) (by omega) ?_
      intro j hj hji
      by_cases he : j = a - 1
      · exact he ▸ h
      · exact inside j (by omega) (by omega)
  have hab : a + (b - a) = b := by omega
  refine ⟨a, b - a, ⟨bubble_iff.mpr ⟨by omega, by omega, by rwa [hab], leftEnd,
    by simpa [hab] using hb.2⟩, ha, by omega⟩, ?_⟩
  intro c q hc hci hic
  obtain ⟨_, _, hfree, hleft, hright⟩ := bubble_iff.mp hc
  have hca : c = a := by
    rcases lt_trichotomy c a with h | h | h
    · exact False.elim ((leftEnd.resolve_left (by omega)) (hfree _ (by omega) (by omega)))
    · exact h
    · exact False.elim ((hleft.resolve_left (by omega)) (inside _ (by omega) (by omega)))
  refine ⟨hca, ?_⟩
  rcases lt_trichotomy (c + q) b with h | h | h
  · exact False.elim (hright (inside _ (by omega) h))
  · omega
  · exact False.elim (hb.2 (hfree _ (by omega) h))

-- Mark either the first vertex of each bubble or all its vertices.
private def Marked {n : ℕ} (σ : DiagramMap n) (first : Bool) (x : ℕ × ℕ) (i : ℕ) :=
  IsBubble σ x.2 x.1 ∧ x.2 ≤ i ∧ i < x.2 + x.1 ∧ (first = true → x.2 = i)

private def Eligible {n : ℕ} (σ : DiagramMap n) (first : Bool) (i : ℕ) :=
  Free σ i ∧ (first = true → i = 0 ∨ ¬Free σ (i - 1))

private theorem marked_at_vertex {n : ℕ} (σ : DiagramMap n) (first : Bool) (i : ℕ) :
    ∑ x ∈ Icc 1 (2 * n) ×ˢ range (2 * n), bit (Marked σ first x i) =
      bit (Eligible σ first i) := by
  classical
  by_cases h : Eligible σ first i
  · obtain ⟨a, p, ⟨hb, hai, hip⟩, hu⟩ := unique_bubble h.1
    obtain ⟨hp, hbound, hrun, _, _⟩ := bubble_iff.mp hb
    have hm : Marked σ first (p, a) i := by
      refine ⟨hb, hai, hip, fun hf => ?_⟩
      rcases h.2 hf with rfl | hn
      · omega
      · by_contra hne
        exact hn (hrun _ (by omega) (by omega))
    rw [sum_eq_single (p, a)]
    · simp [bit, h, hm]
    · intro ⟨q, b⟩ _ hne
      have hn : ¬Marked σ first (q, b) i := by
        intro hh
        obtain ⟨rfl, rfl⟩ := hu b q hh.1 hh.2.1 hh.2.2.1
        exact hne rfl
      simp [bit, hn]
    · simp [mem_Icc, show 1 ≤ p by omega, show p ≤ 2 * n by omega,
        show a < 2 * n by omega]
  · simp only [bit, h, ↓reduceIte]
    apply sum_eq_zero
    intro ⟨p, a⟩ _
    apply ite_eq_right
    rintro ⟨hb, ha, hp, hf⟩
    obtain ⟨_, _, hr, hl, _⟩ := bubble_iff.mp hb
    exact h ⟨hr i ha hp, fun ht => hf ht ▸ hl⟩

private theorem marked_in_bubble {n : ℕ} (σ : DiagramMap n) (first : Bool) (p a : ℕ) :
    ∑ i ∈ range (2 * n), bit (Marked σ first (p, a) i) =
      (if first then 1 else (p : ℚ)) * bit (IsBubble σ a p) := by
  classical
  by_cases h : IsBubble σ a p
  · obtain ⟨hp, hle, _⟩ := bubble_iff.mp h
    have ha : a < 2 * n := by omega
    cases first
    · simp only [Marked, bit, h, true_and, Bool.false_eq_true, false_implies,
        and_true, Bool.false_eq_true, ↓reduceIte, mul_one, sum_boole]
      have he : ((range (2 * n)).filter fun i => a ≤ i ∧ i < a + p) = Ico a (a + p) := by
        ext i
        simp only [mem_filter, mem_range, mem_Ico]
        omega
      simp [he]
    · have hm (i : ℕ) : Marked σ true (p, a) i ↔ a = i := by
        simp [Marked, h]
        omega
      simp [bit, hm, mem_range, ha, h]
  · simp [bit, Marked, h]

private noncomputable def moment (n : ℕ) (first : Bool) : ℚ :=
  ∑ p ∈ Icc 1 (2 * n), (if first then 1 else (p : ℚ)) * bubbleCount n p

private theorem moment_eq (n : ℕ) (first : Bool) :
    moment n first =
      ∑ i ∈ range (2 * n), ∑ σ ∈ diagrams n, bit (Eligible σ first i) := by
  classical
  simp_rw [← marked_at_vertex]
  rw [sum_comm]
  simp_rw [sum_comm (s := range (2 * n)) (t := Icc 1 (2 * n) ×ˢ range (2 * n))]
  simp_rw [sum_product, marked_in_bubble, ← mul_sum, sum_bit]
  unfold moment bubbleCount diagrams
  push_cast
  simp_rw [mul_sum]
  rw [sum_comm]

private noncomputable def count {n : ℕ} (s : Finset (DiagramMap n))
    (P : DiagramMap n → Prop) : ℚ := ∑ σ ∈ s, bit (P σ)

private theorem diagram_relabel {n : ℕ} (e : Equiv.Perm (Fin (2 * n))) (σ : DiagramMap n) :
    (e.arrowCongr e σ ∈ diagrams n) ↔ σ ∈ diagrams n := by
  simp only [diagrams, mem_filter, mem_univ, true_and, IsLinearChordDiagram]
  constructor
  · intro h i
    simpa [Equiv.arrowCongr] using h (e i)
  · intro h i
    obtain ⟨j, rfl⟩ := e.surjective i
    simpa [Equiv.arrowCongr] using h j

-- Swapping two possible partners of a vertex gives equal fibers. Summing the
-- fibers then determines their size without enumerating all matchings.
private theorem partner_count {n : ℕ} (s : Finset (DiagramMap n)) (u : Finset (Fin (2 * n)))
    (a b : Fin (2 * n)) (hb : b ∈ u) (ha : a ∉ u)
    (partner : ∀ σ ∈ s, σ a ∈ u)
    (invariant : ∀ c ∈ u, ∀ σ, let e := Equiv.swap b c
      e.arrowCongr e σ ∈ s ↔ σ ∈ s) :
    count s (fun σ => σ a = b) = s.card / (u.card : ℚ) := by
  classical
  have same (c) (hc : c ∈ u) : count s (fun σ => σ a = b) = count s (fun σ => σ a = c) := by
    let e := Equiv.swap b c
    have ea : e a = a := Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hb))
      (fun h => ha (h ▸ hc))
    apply sum_equiv (e.arrowCongr e) (fun σ => (invariant c hc σ).symm)
    intro σ _
    have he : e.arrowCongr e σ a = c ↔ σ a = b := by
      calc
        e.arrowCongr e σ a = c ↔ e (σ a) = e b := by
          have hb' : e b = c := Equiv.swap_apply_left _ _
          have ea' : e.symm a = a := e.symm_apply_eq.mpr ea.symm
          simp [Equiv.arrowCongr, ea', hb']
        _ ↔ _ := e.injective.eq_iff
    exact congrArg bit (propext he.symm)
  have hsum : (∑ c ∈ u, count s (fun σ => σ a = c)) = s.card := by
    unfold count
    rw [sum_comm]
    trans ∑ _σ ∈ s, (1 : ℚ)
    · apply sum_congr rfl
      intro σ hσ
      rw [sum_eq_single_of_mem (σ a) (partner σ hσ)]
      · simp [bit]
      · intro x _ hx
        simp [bit, Ne.symm hx]
    · simp
  rw [sum_congr rfl (fun c hc => (same c hc).symm)] at hsum
  have hn : (u.card : ℚ) ≠ 0 := by exact_mod_cast (card_pos.mpr ⟨b, hb⟩).ne'
  apply (eq_div_iff hn).mpr
  simpa [mul_comm] using hsum

private theorem single_count {n : ℕ} (a b : Fin (2 * n)) (hab : a ≠ b) :
    count (diagrams n) (fun σ => σ a = b) = (diagrams n).card / (2 * n - 1 : ℚ) := by
  classical
  have h := partner_count (diagrams n) (univ.erase a) a b (by simp [hab.symm]) (by simp)
    (fun σ hσ => by simpa using ((mem_filter.mp hσ).2 a).1)
    (fun _ _ => diagram_relabel _)
  simpa [card_erase_of_mem, Nat.cast_sub (show 1 ≤ 2 * n by have := a.isLt; omega)] using h

private theorem double_count {n : ℕ} (a b c d : Fin (2 * n))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    count (diagrams n) (fun σ => σ a = b ∧ σ c = d) =
      ((diagrams n).card / (2 * n - 1 : ℚ)) / (2 * n - 3) := by
  classical
  let s := (diagrams n).filter fun σ => σ a = b
  let u := ((univ.erase a).erase b).erase c
  have mem_u (x) : x ∈ u ↔ x ≠ c ∧ x ≠ b ∧ x ≠ a := by simp [u]
  have h := partner_count s u c d ((mem_u d).mpr ⟨hcd.symm, hbd.symm, had.symm⟩)
    (by simp [u]) (by
      intro σ hσ
      obtain ⟨hσ, he⟩ := mem_filter.mp hσ
      have hD := (mem_filter.mp hσ).2
      have hba : σ b = a := he ▸ (hD a).2
      apply (mem_u _).mpr
      exact ⟨(hD c).1, fun h => hac ((hD c).2.symm.trans (h ▸ hba)).symm,
        fun h => hbc ((hD c).2.symm.trans (h ▸ he)).symm⟩) (by
      intro x hx σ
      obtain ⟨_, hxb, hxa⟩ := (mem_u x).mp hx
      let e := Equiv.swap d x
      have ea : e a = a := Equiv.swap_apply_of_ne_of_ne had hxa.symm
      have eb : e b = b := Equiv.swap_apply_of_ne_of_ne hbd hxb.symm
      change e.arrowCongr e σ ∈ s ↔ σ ∈ s
      simp only [s, mem_filter, diagram_relabel]
      apply and_congr_right
      intro _
      calc
        e.arrowCongr e σ a = b ↔ e.arrowCongr e σ (e a) = e b := by rw [ea, eb]
        _ ↔ σ a = b := by simp [Equiv.arrowCongr])
  have hs : (s.card : ℚ) = (diagrams n).card / (2 * n - 1 : ℚ) := by
    simpa only [count, sum_bit, s] using single_count a b hab
  have hu : (u.card : ℚ) = 2 * n - 3 := by
    have h3 : 3 ≤ 2 * n := by
      have hle := card_le_univ ({a, b, c} : Finset (Fin (2 * n)))
      simpa [hab, hac, hbc] using hle
    simp [u, card_erase_of_mem, hab.symm, hac.symm, hbc.symm,
      Nat.cast_sub (by omega : 1 ≤ 2 * n), Nat.cast_sub (by omega : 1 ≤ 2 * n - 1),
      Nat.cast_sub (by omega : 1 ≤ 2 * n - 1 - 1)]
    ring
  rw [hs, hu] at h
  convert h using 1
  unfold count s
  rw [sum_filter]
  apply sum_congr rfl
  intro σ _
  by_cases he : σ a = b <;> simp [bit, he]

-- A short chord is recorded by its left endpoint.
private def Edge {n : ℕ} (σ : DiagramMap n) (i : ℕ) : Prop :=
  ∃ hi : i < 2 * n, (σ ⟨i, hi⟩ : ℕ) = i + 1

private theorem edge_iff {n i : ℕ} (σ : DiagramMap n) (hi : i + 1 < 2 * n) :
    Edge σ i ↔ σ ⟨i, by omega⟩ = ⟨i + 1, hi⟩ :=
  ⟨fun h => Fin.ext h.choose_spec, fun h => ⟨by omega, congrArg Fin.val h⟩⟩

private theorem no_last_edge {n i : ℕ} (σ : DiagramMap n) (hi : 2 * n ≤ i + 1) :
    ¬Edge σ i := by
  rintro ⟨h, he⟩
  have := (σ ⟨i, h⟩).isLt
  omega

private theorem free_zero {n : ℕ} (σ : DiagramMap n) (hn : 0 < 2 * n) :
    Free σ 0 ↔ ¬Edge σ 0 := by
  simp [Free, Edge, hn, IsShortChordVertex, eq_comm]

private theorem edge_at_right {n i : ℕ} {σ : DiagramMap n} (hD : IsLinearChordDiagram n σ)
    (hi : i + 1 < 2 * n) : Edge σ i ↔ (σ ⟨i + 1, hi⟩ : ℕ) = i := by
  rw [edge_iff σ hi]
  let a : Fin (2 * n) := ⟨i, by omega⟩
  let b : Fin (2 * n) := ⟨i + 1, hi⟩
  change σ a = b ↔ (σ b : ℕ) = i
  constructor
  · intro h
    exact congrArg Fin.val (show σ b = a by rw [← h, (hD a).2])
  · intro h
    have he : σ b = a := Fin.ext h
    rw [← he, (hD b).2]

private theorem free_succ {n i : ℕ} {σ : DiagramMap n} (hD : IsLinearChordDiagram n σ)
    (hi : i + 1 < 2 * n) : Free σ (i + 1) ↔ ¬Edge σ i ∧ ¬Edge σ (i + 1) := by
  rw [edge_at_right hD hi]
  simp [Free, Edge, hi, IsShortChordVertex]
  omega

private theorem edges_disjoint {n i : ℕ} {σ : DiagramMap n} (hD : IsLinearChordDiagram n σ)
    (hi : i + 1 < 2 * n) (he : Edge σ i) : ¬Edge σ (i + 1) := by
  have h := (edge_at_right hD hi).mp he
  rintro ⟨_, he'⟩
  omega

private theorem edge_count {n i : ℕ} (hi : i + 1 < 2 * n) :
    count (diagrams n) (fun σ => Edge σ i) = (diagrams n).card / (2 * n - 1 : ℚ) := by
  simpa only [count, edge_iff _ hi] using
    single_count (n := n) ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp)

private theorem edge_pair_count {n i : ℕ} (hi : i + 3 < 2 * n) :
    count (diagrams n) (fun σ => Edge σ i ∧ Edge σ (i + 2)) =
      ((diagrams n).card / (2 * n - 1 : ℚ)) / (2 * n - 3) := by
  have h1 : i + 1 < 2 * n := by omega
  simpa only [count, edge_iff _ h1, edge_iff _ hi] using
    double_count (n := n) ⟨i, by omega⟩ ⟨i + 1, h1⟩ ⟨i + 2, by omega⟩ ⟨i + 3, hi⟩
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

-- These local counts distinguish the first vertex, the second vertex, and the
-- remaining vertices, where a new bubble must follow a short chord.
private theorem at_zero {n : ℕ} (hn : 0 < 2 * n) (first : Bool) :
    count (diagrams n) (fun σ => Eligible σ first 0) =
      (diagrams n).card - count (diagrams n) (fun σ => Edge σ 0) := by
  unfold count
  calc
    _ = ∑ σ ∈ diagrams n, (1 - bit (Edge σ 0)) := by
      apply sum_congr rfl
      intro σ _
      by_cases h : Edge σ 0 <;> simp [Eligible, bit, free_zero σ hn, h]
    _ = _ := by simp [sum_sub_distrib]

private theorem all_at_succ {n i : ℕ} (hi : i + 1 < 2 * n) :
    count (diagrams n) (fun σ => Eligible σ false (i + 1)) =
      (diagrams n).card - count (diagrams n) (fun σ => Edge σ i) -
        count (diagrams n) (fun σ => Edge σ (i + 1)) := by
  unfold count
  calc
    _ = ∑ σ ∈ diagrams n, (1 - bit (Edge σ i) - bit (Edge σ (i + 1))) := by
      apply sum_congr rfl
      intro σ hσ
      have hD := (mem_filter.mp hσ).2
      by_cases h : Edge σ i
      · simp [bit, Eligible, free_succ hD hi, h, edges_disjoint hD hi h]
      · by_cases h' : Edge σ (i + 1) <;> simp [bit, Eligible, free_succ hD hi, h, h']
    _ = _ := by simp [sum_sub_distrib]

private theorem start_at_one {n : ℕ} (hn : 1 < 2 * n) :
    count (diagrams n) (fun σ => Eligible σ true 1) = 0 := by
  apply sum_eq_zero
  intro σ hσ
  have hD := (mem_filter.mp hσ).2
  have h : ¬Eligible σ true 1 := by
    rintro ⟨hf, he⟩
    have h0 := ((free_succ (i := 0) hD hn).mp hf).1
    exact (he rfl).resolve_left (by decide) ((free_zero σ (by omega)).mpr h0)
  simp [bit, h]

private theorem start_at_add_two {n i : ℕ} (hi : i + 2 < 2 * n) :
    count (diagrams n) (fun σ => Eligible σ true (i + 2)) =
      count (diagrams n) (fun σ => Edge σ i) -
        count (diagrams n) (fun σ => Edge σ i ∧ Edge σ (i + 2)) := by
  unfold count
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro σ hσ
  have hD := (mem_filter.mp hσ).2
  have h1 : i + 1 < 2 * n := by omega
  have he : Eligible σ true (i + 2) ↔ Edge σ i ∧ ¬Edge σ (i + 2) := by
    simp only [Eligible, show i + 2 - 1 = i + 1 by omega, Nat.add_eq_zero_iff, and_false,
      Nat.reduceEqDiff, false_or, forall_const, free_succ hD hi, free_succ hD h1]
    have := edges_disjoint hD h1
    tauto
  by_cases h : Edge σ i <;> by_cases h' : Edge σ (i + 2) <;> simp [bit, he, h, h']

private theorem diagrams_pos {n : ℕ} (hn : 0 < n) : 0 < (diagrams n).card := by
  -- Match corresponding vertices in the first and second halves of the line.
  let σ : DiagramMap n := fun i => if h : (i : ℕ) < n then ⟨i + n, by omega⟩
    else ⟨i - n, by omega⟩
  apply card_pos.mpr
  refine ⟨σ, mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩⟩
  by_cases hi : (i : ℕ) < n
  · have h : ¬(i : ℕ) + n < n := by omega
    simp [σ, hi, h, Fin.ext_iff, Nat.ne_of_gt hn]
  · have h : (i : ℕ) - n < n := by have := i.isLt; omega
    simp [σ, hi, h, Fin.ext_iff, Nat.sub_add_cancel (by omega : n ≤ (i : ℕ))]
    omega

private theorem sum_positions (k : ℕ) (f : ℕ → ℚ) (v : ℚ)
    (hv : ∀ i < k + 1, f (i + 2) = v) :
    ∑ i ∈ range (k + 4), f i = f 0 + f 1 + (k + 1 : ℚ) * v + f (k + 3) := by
  rw [sum_range_succ, sum_range_succ', sum_range_succ']
  rw [sum_congr rfl (fun i hi => hv i (mem_range.mp hi))]
  simp
  ring

private theorem moments {n : ℕ} (hn : 2 ≤ n) :
    let D : ℚ := (diagrams n).card
    let E := D / (2 * n - 1)
    let F := E / (2 * n - 3)
    moment n false = 2 * (D - E) + (2 * n - 2) * (D - 2 * E) ∧
      moment n true = D + (2 * n - 3) * (E - F) := by
  classical
  intro D E F
  let k := 2 * n - 4
  have hk : 2 * n = k + 4 := by dsimp [k]; omega
  have hq : (2 * n : ℚ) = k + 4 := by exact_mod_cast hk
  have e (i : ℕ) (hi : i + 1 < 2 * n) :
      count (diagrams n) (fun σ => Edge σ i) = E := edge_count hi
  have last : count (diagrams n) (fun σ => Edge σ (k + 3)) = 0 := by
    apply sum_eq_zero
    intro σ _
    simp [bit, no_last_edge σ (show 2 * n ≤ k + 3 + 1 by omega)]
  have lastPair : count (diagrams n) (fun σ => Edge σ (k + 1) ∧ Edge σ (k + 3)) = 0 := by
    apply sum_eq_zero
    intro σ _
    simp [bit, no_last_edge σ (show 2 * n ≤ k + 3 + 1 by omega)]
  have h0 (first) : count (diagrams n) (fun σ => Eligible σ first 0) = D - E := by
    rw [at_zero (by omega), e 0 (by omega)]
  have interior (j : ℕ) (hj : j + 2 < 2 * n) :
      count (diagrams n) (fun σ => Eligible σ false (j + 1)) = D - 2 * E := by
    rw [all_at_succ (by omega), e _ (by omega), e _ hj]
    dsimp [D]
    ring
  have middle (i : ℕ) (hi : i < k + 1) :
      count (diagrams n) (fun σ => Eligible σ true (i + 2)) = E - F := by
    rw [start_at_add_two (by omega), e _ (by omega), edge_pair_count (by omega)]
  have total (first) : moment n first =
      ∑ i ∈ range (k + 4), count (diagrams n) (fun σ => Eligible σ first i) := by
    simpa only [← hk, count] using moment_eq n first
  constructor
  · rw [total, sum_positions k _ (D - 2 * E) (fun i hi => interior (i + 1) (by omega)),
      h0, interior 0 (by omega), all_at_succ (i := k + 2) (by omega), last, e _ (by omega)]
    change _ + (D - E - 0) = _
    rw [hq]
    ring
  · rw [total, sum_positions k _ (E - F) middle, h0, start_at_one (by omega),
      start_at_add_two (i := k + 1) (by omega), e _ (by omega), lastPair, hq]
    ring

end mean_bubble_size

namespace sum_mul_bubbleCount

open Finset Equiv.Perm mean_bubble_size

private theorem weighted_moment {n : ℕ} (hn : 2 ≤ n) :
    moment n false = (2 * n - 2) * (diagrams n).card := by
  have hq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  rw [(moments hn).1]
  field_simp [show (2 * n - 1 : ℚ) ≠ 0 by linarith]
  ring

-- The nontrivial cycles of a diagram are its chords, and they cover all vertices.
private theorem diagram_iff_cycleType {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) :
    IsLinearChordDiagram n π ↔ π.cycleType = Multiset.replicate n 2 := by
  have hsum := π.sum_cycleType
  constructor
  · intro h
    have hs : π.support = univ := eq_univ_of_forall fun i => mem_support.mpr (h i).1
    have hpow : π ^ 2 = 1 := Equiv.ext fun i => (h i).2
    have htype := cycleType_of_pow_prime_eq_one hpow
    rw [htype, hs] at hsum
    simp at hsum
    rwa [show π.cycleType.card = n by omega] at htype
  · intro h
    have hpow : π ^ 2 = 1 := pow_prime_eq_one_iff.mpr fun c hc =>
      Multiset.eq_of_mem_replicate (h ▸ hc)
    have hs : π.support = univ := by
      apply eq_univ_of_card
      simp [← hsum, h, mul_comm]
    intro i
    exact ⟨mem_support.mp (hs ▸ mem_univ i), DFunLike.congr_fun hpow i⟩

private theorem diagram_count {n : ℕ} (hn : n ≠ 0) :
    ((diagrams n).card : ℚ) = (2 * n).factorial / (2 ^ n * n.factorial) := by
  classical
  let perms := univ.filter fun π : Equiv.Perm (Fin (2 * n)) =>
    π.cycleType = Multiset.replicate n 2
  have hcard : perms.card = (diagrams n).card := by
    apply card_nbij (fun π : Equiv.Perm (Fin (2 * n)) => (π : Fin (2 * n) → Fin (2 * n)))
    · intro π hπ
      exact mem_filter.mpr ⟨mem_univ _, (diagram_iff_cycleType π).mpr (mem_filter.mp hπ).2⟩
    · exact fun _ _ _ _ h => DFunLike.coe_injective h
    · intro σ hσ
      have hd := (mem_filter.mp hσ).2
      let π := Function.Involutive.toPerm σ (fun i => (hd i).2)
      exact ⟨π, mem_filter.mpr ⟨mem_univ _, (diagram_iff_cycleType π).mp hd⟩, rfl⟩
  have h : perms.card * (2 ^ n * n.factorial) = (2 * n).factorial := by
    simpa [perms, Multiset.toFinset_replicate, Multiset.mem_replicate, hn, mul_comm n 2] using
      card_of_cycleType_mul_eq (Fin (2 * n)) (Multiset.replicate n 2)
  rw [← hcard]
  apply (eq_div_iff (by positivity)).mpr
  exact_mod_cast h

end sum_mul_bubbleCount

open mean_bubble_size sum_mul_bubbleCount in
/-- **First moment of bubble sizes in linear chord diagrams.** For every natural number
$n \ge 2$, let $B_{n,p}$ be the total number of bubbles of size $p$ over all linear chord diagrams
on $2n$ vertices. Then
$$\sum_{p=1}^{2n} p\,B_{n,p} = \frac{(2n-1)!}{2^{n-2}\,(n-2)!}.$$

The hypothesis $n \ge 2$ is added because the right side involves $(n-2)!$.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Lemma 4 (`jis-2024-24.4.2-lem-4`). -/
theorem sum_mul_bubbleCount (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (p : ℚ) * bubbleCount n p) =
      (2 * n - 1).factorial / (2 ^ (n - 2) * (n - 2).factorial) := by
  change moment n false = _
  rw [weighted_moment hn, diagram_count (by omega), ← Nat.mul_factorial_pred (by omega : 2 * n ≠ 0)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

open mean_bubble_size in
/-- **Mean bubble size.** Let $B_{n,p}$ be the total number of bubbles of size $p$ in all linear
chord diagrams on $2n$ vertices. For every integer $n \ge 2$, the mean bubble size satisfies
$$\frac{\sum_{p=1}^{2n} p\,B_{n,p}}{\sum_{p=1}^{2n} B_{n,p}} = \frac{2(2n-1)(n-1)}{4n-5}.$$

The hypothesis $n \ge 2$ is added: for $n = 1$ there are no bubbles.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 5 (`jis-2024-24.4.2-thm-5`). -/
theorem mean_bubble_size (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (p : ℚ) * bubbleCount n p) /
        (∑ p ∈ Finset.Icc 1 (2 * n), (bubbleCount n p : ℚ)) =
      2 * (2 * n - 1) * (n - 1) / (4 * n - 5) := by
  have hq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℚ) < (diagrams n).card := by exact_mod_cast diagrams_pos (by omega : 0 < n)
  have h1 : (2 * n - 1 : ℚ) ≠ 0 := by linarith
  have hs : moment n true = (4 * n - 5) * (diagrams n).card / (2 * n - 1) := by
    rw [(moments hn).2]
    have h3 : (2 * n - 3 : ℚ) ≠ 0 := by linarith
    field_simp [h1, h3]
    ring
  simpa only [moment, Bool.false_eq_true, ↓reduceIte, one_mul] using
    (show moment n false / moment n true = _ by
      rw [sum_mul_bubbleCount.weighted_moment hn, hs]
      have h4 : (4 * n - 5 : ℚ) ≠ 0 := by linarith
      field_simp [h1, h4, hD.ne'])

end

end MetaMathlibExt
