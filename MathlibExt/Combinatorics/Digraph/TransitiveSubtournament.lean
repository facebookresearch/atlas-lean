/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases

/-!
# Transitive subtournaments and Erdős Problem 1216

Every tournament on fifteen vertices has a transitive subtournament of order five.
This refutes the proposed formula for the transitive subtournament number.

In a tournament on fifteen vertices with no transitive five, splitting at a vertex gives two
seven-vertex neighborhoods with no transitive four. Repeating the split shows that a transitive
chain of length `j ≤ 4` has exactly `2 ^ (4 - j) - 1` common successors. For a fixed transitive
four, these intersection sizes determine the number of vertices with each adjacency profile.
Each four-bit mask from 0 through 14 labels exactly one vertex.

The four basis rows of the adjacency matrix are then fixed. The proof enumerates the possible
successor sets at masks 4, 9 and 10. No choice of these three rows simultaneously orients their
mutual edges and gives every ordered chain of recorded vertices the required successor count.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1216, https://www.erdosproblems.com/1216 (status
DISPROVED). UnsolvedMath record UM-30007257 (`EP-1216`), dataset ulamai/UnsolvedMath v1.8.0.

`f(n)` is the largest such number (the source's "let f(n) be such that" with the asked equality
means the optimal value), as `sSup`; the set is bounded by `n`. The equality is read for every `n ≥
1`. formal-conjectures has no statement.
-/

/-- **Tournaments.** Let $n \in \mathbb{N}$. A relation $T$ on $\{0, \dots, n-1\}$ is a
tournament when $T(x, x)$ holds for no $x$ and, for all distinct $x$ and $y$, exactly one of
$T(x, y)$ and $T(y, x)$ holds. -/
def IsTournament {n : ℕ} (T : Fin n → Fin n → Prop) : Prop :=
  (∀ x, ¬ T x x) ∧ ∀ x y, x ≠ y → (T x y ↔ ¬ T y x)

/-- **Transitivity on a vertex set.** Let $n \in \mathbb{N}$, let $T$ be a relation on
$\{0, \dots, n-1\}$ and let $S$ be a set of its elements. Then $T$ is transitive on $S$ when, for
all $x, y, z \in S$, $T(x, y)$ and $T(y, z)$ imply $T(x, z)$. For a tournament $T$ this says that
the subtournament of $T$ on $S$ is transitive. -/
def IsTransitiveOn {n : ℕ} (T : Fin n → Fin n → Prop) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, T x y → T y z → T x z

/-- **Transitive subtournament number.** For $n \in \mathbb{N}$, $f(n)$ is the largest $m$ such
that every tournament $T$ on $\{0, \dots, n-1\}$ is transitive on some set of exactly $m$
vertices, that is, contains a transitive subtournament on $m$ vertices.

Such $m$ exist (for instance $m = 0$) and are at most $n$, so the largest one exists. -/
noncomputable def transitiveSubtournamentNumber (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ T : Fin n → Fin n → Prop, IsTournament T →
    ∃ S : Finset (Fin n), S.card = m ∧ IsTransitiveOn T S}

/-- **Erdős Problem 1216 (the Erdős–Moser formula).** For every $n \ge 1$,
$f(n) = \lfloor \log_2 n \rfloor + 1$, where $f(n)$ is the largest $m$ such that every tournament
on $n$ vertices contains a transitive subtournament on $m$ vertices. -/
def transitiveSubtournamentNumberEqLogTwo : Prop :=
  ∀ n : ℕ, 1 ≤ n → transitiveSubtournamentNumber n = Nat.log 2 n + 1

private abbrev V := Fin 15

private abbrev Rel := V → V → Prop

private def HasChain (T : Rel) (s : Finset V) (k : ℕ) : Prop :=
  ∃ u ⊆ s, u.card = k ∧ IsTransitiveOn T u

/-- Extending a transitive subtournament at either end. -/
private theorem extendChain {T : Rel} (ht : IsTournament T) {s u : Finset V} {x : V}
    (hx : x ∈ s) (hu : u ⊆ s) (h : IsTransitiveOn T u)
    (he : (∀ y ∈ u, T x y) ∨ (∀ y ∈ u, T y x)) : HasChain T s (u.card + 1) := by
  have hxx := ht.1 x
  have asymm (a b : V) : T a b → ¬ T b a := by
    by_cases e : a = b
    · subst b
      exact fun hab => (ht.1 a hab).elim
    · exact (ht.2 a b e).mp
  have hn : x ∉ u := by
    intro hxu
    rcases he with he | he <;> exact hxx (he x hxu)
  refine ⟨insert x u, Finset.insert_subset hx hu, Finset.card_insert_of_notMem hn, ?_⟩
  intro a ha b hb c hc hab hbc
  simp only [Finset.mem_insert] at ha hb hc
  rcases ha with rfl | ha <;> rcases hb with rfl | hb <;> rcases hc with rfl | hc <;>
    first | contradiction | exact h _ ha _ hb _ hc hab hbc |
      rcases he with he | he <;> solve_by_elim

private noncomputable def outs (T : Rel) (s : Finset V) (x : V) : Finset V := by
  classical
  exact s.filter fun y => T x y

private noncomputable def ins (T : Rel) (s : Finset V) (x : V) : Finset V := by
  classical
  exact s.filter fun y => T y x

private theorem split_card {T : Rel} (ht : IsTournament T) {s : Finset V} {x : V} (hx : x ∈ s) :
    (outs T s x).card + (ins T s x).card + 1 = s.card := by
  classical
  have hd : Disjoint (outs T s x) (ins T s x) := by
    simp only [Finset.disjoint_left, outs, ins, Finset.mem_filter]
    rintro y ⟨_, hxy⟩ ⟨_, hyx⟩
    exact ((ht.2 x y (fun e => ht.1 x (e ▸ hxy))).mp hxy) hyx
  have he : insert x (outs T s x ∪ ins T s x) = s := by
    ext y
    simp only [Finset.mem_insert, Finset.mem_union, outs, ins, Finset.mem_filter]
    by_cases e : y = x
    · simp [e, hx]
    · rw [ht.2 y x e]
      tauto
  have hn : x ∉ outs T s x ∪ ins T s x := by simp [outs, ins, ht.1]
  rw [← Finset.card_union_of_disjoint hd, ← Finset.card_insert_of_notMem hn, he]

private theorem avoid_neighbors {T : Rel} (ht : IsTournament T) {s : Finset V} {x : V}
    (hx : x ∈ s) {k : ℕ} (h : ¬ HasChain T s (k + 1)) :
    ¬ HasChain T (outs T s x) k ∧ ¬ HasChain T (ins T s x) k := by
  classical
  constructor <;> rintro ⟨u, hu, rfl, htr⟩ <;> apply h
  · apply extendChain ht hx (hu.trans (Finset.filter_subset ..)) htr
    exact Or.inl fun y hy => (Finset.mem_filter.mp (hu hy)).2
  · apply extendChain ht hx (hu.trans (Finset.filter_subset ..)) htr
    exact Or.inr fun y hy => (Finset.mem_filter.mp (hu hy)).2

/-- The elementary tournament bound, obtained by adjoining a pivot to one neighborhood. -/
private theorem card_lt_pow {T : Rel} (ht : IsTournament T) (k : ℕ) (s : Finset V)
    (h : ¬ HasChain T s (k + 1)) : s.card < 2 ^ k := by
  induction k generalizing s with
  | zero =>
    by_contra! hn
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by simpa using hn)
    exact h ⟨{x}, Finset.singleton_subset_iff.mpr hx, by simp, by simp [IsTransitiveOn, ht.1]⟩
  | succ k ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact Nat.two_pow_pos _
    obtain ⟨ho, hi⟩ := avoid_neighbors ht hx h
    have := ih _ ho
    have := ih _ hi
    have := split_card ht hx
    rw [pow_succ]
    omega

private structure Tight (T : Rel) (k : ℕ) (s : Finset V) : Prop where
  size : s.card + 1 = 2 ^ k
  avoid : ¬ HasChain T s (k + 1)

private theorem Tight.out {T : Rel} (ht : IsTournament T) {k : ℕ} {s : Finset V}
    (h : Tight T (k + 1) s) {x : V} (hx : x ∈ s) : Tight T k (outs T s x) := by
  obtain ⟨ho, hi⟩ := avoid_neighbors ht hx h.avoid
  have := card_lt_pow ht k _ ho
  have := card_lt_pow ht k _ hi
  have := split_card ht hx
  have hs := h.size
  rw [pow_succ] at hs
  exact ⟨by omega, ho⟩


/-- Common successors of a list of vertices, starting in a specified set. -/
private noncomputable def common {ι : Type} (f : ι → V → Prop) (s : Finset V) :
    List ι → Finset V
  | [] => s
  | i :: l => common f (by classical exact s.filter (f i)) l

private theorem common_size {ι : Type} {T : Rel} (ht : IsTournament T) (p : ι → V)
    (l : List ι) {s : Finset V} {k : ℕ} (hs : Tight T k s) (hl : l.length ≤ k)
    (hm : ∀ i ∈ l, p i ∈ s) (hp : l.Pairwise fun i j => T (p i) (p j)) :
    (common (fun i => T (p i)) s l).card + 1 = 2 ^ (k - l.length) := by
  classical
  induction l generalizing s k with
  | nil => simpa [common] using hs.size
  | cons i l ih =>
    cases k with
    | zero => simp at hl
    | succ k =>
      obtain ⟨hi, hp⟩ := List.pairwise_cons.mp hp
      have ht' := hs.out ht (hm i (by simp))
      have h := ih ht' (by simpa using hl) (fun j hj =>
        Finset.mem_filter.mpr ⟨hm j (by simp [hj]), hi j hj⟩) hp
      simpa [common, outs] using h

/-- A profile specifies which of the distinguished vertices point to a vertex. -/
private noncomputable def fiber {ι : Type} (f : ι → V → Prop) (s : Finset V)
    (l : List ι) (b : ι → Prop) : Finset V := by
  classical
  exact s.filter fun v => ∀ i ∈ l, f i v ↔ b i

/-- All intersection sizes determine all profile sizes, by splitting off one coordinate. -/
private theorem fiber_card_eq {ι : Type} (f g : ι → V → Prop) (l : List ι)
    (b : ι → Prop) (s t : Finset V)
    (h : ∀ u : List ι, u.Sublist l → (common f s u).card = (common g t u).card) :
    (fiber f s l b).card = (fiber g t l b).card := by
  classical
  induction l generalizing s t with
  | nil => simpa [fiber, common] using h [] (.slnil)
  | cons i l ih =>
    have h₀ := ih s t fun u hu => h u (hu.cons i)
    have h₁ := ih (s.filter (f i)) (t.filter (g i)) fun u hu => h (i :: u) (hu.cons_cons i)
    have split (F : ι → V → Prop) (a : Finset V) :
        (fiber F a l b).filter (F i) = fiber F (a.filter (F i)) l b := by
      ext v
      simp [fiber, and_right_comm, and_assoc, and_left_comm]
    by_cases hb : b i
    · simpa [fiber, hb, Finset.filter_filter, and_assoc] using h₁
    · have ha := Finset.card_filter_add_card_filter_not (s := fiber f s l b) (p := f i)
      have hc := Finset.card_filter_add_card_filter_not (s := fiber g t l b) (p := g i)
      rw [split] at ha hc
      have he : ((fiber f s l b).filter fun x => ¬ f i x).card =
          ((fiber g t l b).filter fun x => ¬ g i x).card := by omega
      simpa [fiber, hb, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using he

private abbrev I := Fin 4

private def basis : List I := [0, 1, 2, 3]

private def bit (i : I) (v : V) : Bool := v.val.testBit i.val

private def basisLabel (i : I) : V := ⟨2 ^ i.val - 1, by fin_cases i <;> decide⟩

private theorem exists_basis {T : Rel} (ht : IsTournament T)
    (h : Tight T 4 Finset.univ) :
    ∃ p : I → V, basis.Pairwise fun i j => T (p i) (p j) := by
  classical
  have nonempty {k : ℕ} {s : Finset V} (hs : Tight T k s) (hk : 1 < 2 ^ k) : s.Nonempty :=
    Finset.card_pos.mp (by have := hs.size; omega)
  let a : V := 0
  have ha := h.out ht (Finset.mem_univ a)
  obtain ⟨b, hb⟩ := nonempty ha (by decide)
  have hab := (Finset.mem_filter.mp hb).2
  have hb' := ha.out ht hb
  obtain ⟨c, hc⟩ := nonempty hb' (by decide)
  have ⟨hc', hbc⟩ := Finset.mem_filter.mp hc
  have hac := (Finset.mem_filter.mp hc').2
  have hcT := hb'.out ht hc
  obtain ⟨d, hd⟩ := nonempty hcT (by decide)
  obtain ⟨hd', hcd⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd'', hbd⟩ := Finset.mem_filter.mp hd'
  have had := (Finset.mem_filter.mp hd'').2
  exact ⟨![a, b, c, d], by simpa [basis] using And.intro ⟨hab, hac, had⟩ ⟨⟨hbc, hbd⟩, hcd⟩⟩

private theorem mem_common {ι : Type} (f : ι → V → Prop) (l : List ι) (s : Finset V) (v : V) :
    v ∈ common f s l ↔ v ∈ s ∧ ∀ i ∈ l, f i v := by
  classical
  induction l generalizing s with
  | nil => simp [common]
  | cons i l ih => simp [common, ih, and_assoc]

/-- Label the vertices by their four incoming bits from a transitive four.
The intersection sizes agree with the proper subsets of four coordinates. -/
private theorem labeling {T : Rel} (ht : IsTournament T) (h : Tight T 4 Finset.univ) :
    ∃ e : V ≃ V, ∀ i v, T (e (basisLabel i)) (e v) ↔ bit i v := by
  classical
  obtain ⟨p, hp⟩ := exists_basis ht h
  let f i := T (p i)
  let g (i : I) (v : V) : Prop := bit i v
  have sizes (l : List I) (hl : l.Sublist basis) :
      (common f Finset.univ l).card = (common g Finset.univ l).card := by
    have h₁ := common_size ht p l h (show l.length ≤ basis.length from hl.length_le)
      (fun _ _ => Finset.mem_univ _) (hp.sublist hl)
    have model : ∀ u ∈ basis.sublists,
        (Finset.univ.filter (fun v => u.all (fun i => bit i v))).card + 1 =
          2 ^ (4 - u.length) := by decide
    have he : common g Finset.univ l = Finset.univ.filter (fun v => l.all (fun i => bit i v)) := by
      ext
      simp [mem_common, g]
    rw [he]
    exact Nat.add_right_cancel (h₁.trans (model l (List.mem_sublists.mpr hl)).symm)
  have uniqueBits : ∀ a b : V, (∀ i : I, bit i a = bit i b) → a = b := by decide
  have coords : ∀ i : I, i ∈ basis := by decide
  have pick (v : V) : ∃ w : V, ∀ i, f i w ↔ g i v := by
    have he : fiber g Finset.univ basis (fun i => g i v) = {v} := by
      ext w
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hw => uniqueBits _ _ (fun i => Bool.eq_iff_iff.mpr (hw i (coords i))),
        fun e => e ▸ fun _ _ => Iff.rfl⟩
    have hc := fiber_card_eq f g basis (fun i => g i v) _ _ sizes
    rw [he, Finset.card_singleton] at hc
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (hc.symm ▸ Nat.zero_lt_one)
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨w, fun i => hw i (coords i)⟩
  choose a ha using pick
  have hinj : Function.Injective a := fun u v huv => uniqueBits u v (fun i =>
    Bool.eq_iff_iff.mpr ((ha u i).symm.trans (huv ▸ ha v i)))
  let e := Equiv.ofBijective a ((Finite.injective_iff_bijective).mp hinj)
  have order : ∀ i j : I, i < j → T (p i) (p j) := by
    intro i j hij
    have hg : ∀ i : I, basis[i.val]'(i.isLt) = i := by decide
    rw [← hg i, ← hg j]
    exact List.pairwise_iff_getElem.mp hp _ _ _ _ hij
  have actual (j : I) : e (basisLabel j) = p j := by
    apply e.symm.injective
    rw [Equiv.symm_apply_apply]
    apply uniqueBits
    intro i
    have hj := ha (e.symm (p j)) i
    change T (p i) (e (e.symm (p j))) ↔ _ at hj
    rw [Equiv.apply_symm_apply] at hj
    have hb : ∀ i j : I, bit i (basisLabel j) = decide (i < j) := by decide
    rw [hb, Bool.eq_iff_iff, decide_eq_true_eq]
    apply Iff.trans _ hj
    constructor
    · exact order i j
    · intro hij
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exact hlt
      · exact (ht.1 _ hij).elim
      · have hji := order j i hgt
        exact ((ht.2 _ _ (fun eq => ht.1 _ (eq ▸ hij))).mp hij hji).elim
  exact ⟨e, fun i v => actual i ▸ ha v i⟩

private abbrev Row := V × Finset V

private def basisRows : List Row :=
  basis.map fun i => (basisLabel i, Finset.univ.filter fun v => bit i v)

private def Records (T : Rel) (rs : List Row) : Prop :=
  ∀ r ∈ rs, ∀ v, v ∈ r.2 ↔ T r.1 v

/-- Check the common successor count for each ordered chain of recorded vertices. -/
private def counts (rs : List Row) : ℕ → Finset V → Bool
  | 0, s => s.card == 0
  | k + 1, s => s.card + 1 == 2 ^ (k + 1) && rs.all fun (v, r) =>
      v ∉ s || counts rs k (s ∩ r)

private theorem counts_of_tight {T : Rel} (ht : IsTournament T) {rs : List Row}
    (hr : Records T rs) (k : ℕ) (s : Finset V) (hs : Tight T k s) : counts rs k s := by
  classical
  induction k generalizing s with
  | zero => simpa [counts] using hs.size
  | succ k ih =>
    simp only [counts, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨hs.size, ?_⟩
    rintro ⟨v, r⟩ hvr
    by_cases hv : v ∈ s
    · have he : s ∩ r = outs T s v := by
        ext y
        simp only [Finset.mem_inter, outs, Finset.mem_filter]
        rw [hr (v, r) hvr]
      simpa [hv, he] using ih _ (hs.out ht hv)
    · simp [hv]

/-- Edges between two recorded vertices must have opposite entries in their rows. -/
private def oriented (rs : List Row) : Bool :=
  rs.all fun (v, r) => rs.all fun (w, s) =>
    v == w || decide (w ∈ r) != decide (v ∈ s)

private theorem oriented_of_records {T : Rel} (ht : IsTournament T) {rs : List Row}
    (hr : Records T rs) : oriented rs := by
  simp only [oriented, List.all_eq_true]
  rintro ⟨v, r⟩ hvr ⟨w, s⟩ hws
  by_cases h : v = w
  · simp [h]
  · have he := ht.2 _ _ h
    have h₁ := hr (v, r) hvr w
    have h₂ := hr (w, s) hws v
    by_cases e : w ∈ r <;> simp_all

private def labels : Finset V := (basis.map basisLabel).toFinset

private def forced (x : V) : Finset V :=
  ((basis.filter fun i => !(bit i x)).map basisLabel).toFinset

/-- Fill the ten unknown entries of a row and retain those with the required counts. -/
private def candidates (x : V) : Finset (Finset V) :=
  let free := (Finset.univ.erase x) \ labels
  let possible := (free.powersetCard (7 - (forced x).card)).filter fun t =>
    let r := forced x ∪ t
    counts ((x, r) :: basisRows) 4 Finset.univ
  possible.image fun t => forced x ∪ t

private theorem row_mem {T : Rel} (ht : IsTournament T) (hs : Tight T 4 Finset.univ)
    (hb : ∀ i v, T (basisLabel i) v ↔ bit i v) (hr : Records T basisRows)
    {x : V} (hx : x ∉ labels) :
    outs T Finset.univ x ∈ candidates x := by
  classical
  let r := outs T Finset.univ x
  have mem (v : V) : v ∈ r ↔ T x v := by simp [r, outs]
  have hsub : r \ labels ⊆ (Finset.univ.erase x) \ labels := by
    intro v hv
    obtain ⟨hv, hl⟩ := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨fun e =>
      ht.1 _ (e ▸ (mem v).mp hv), Finset.mem_univ _⟩, hl⟩
  have heq : forced x ∪ (r \ labels) = r := by
    have onLabel (i : I) : (T x (basisLabel i) ↔ ¬ bit i x) := by
      have hn : x ≠ basisLabel i := fun e => hx (by
        have hcoord : ∀ j : I, j ∈ basis := by decide
        exact e ▸ List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, hcoord i, rfl⟩))
      rw [ht.2 _ _ hn, hb]
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hf | ⟨hy, _⟩)
      · simp only [forced, List.mem_toFinset, List.mem_map, List.mem_filter,
          Bool.not_eq_true'] at hf
        obtain ⟨i, ⟨_, hi⟩, rfl⟩ := hf
        exact (mem _).mpr ((onLabel i).mpr (by simp [hi]))
      · exact hy
    · intro hy
      by_cases hv : v ∈ labels
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
        have he := (onLabel i).mp ((mem _).mp hy)
        exact Or.inl (List.mem_toFinset.mpr (List.mem_map.mpr
          ⟨i, List.mem_filter.mpr ⟨hi, by simpa using he⟩, rfl⟩))
      · exact Or.inr ⟨hy, hv⟩
  apply Finset.mem_image.mpr
  have hd : Disjoint (forced x) (r \ labels) := by
    apply Finset.disjoint_left.mpr
    intro v hf hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
    exact (Finset.mem_sdiff.mp hv).2 (List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨i, (List.mem_filter.mp hi).1, rfl⟩))
  have hrow := (hs.out ht (Finset.mem_univ x)).size
  change r.card + 1 = 2 ^ 3 at hrow
  have hc := Finset.card_union_of_disjoint hd
  rw [heq] at hc
  refine ⟨r \ labels, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, by omega⟩, ?_⟩,
    heq⟩
  rw [heq]
  apply counts_of_tight ht _ _ _ hs
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact mem
  · exact hr z hz

private theorem relabel_tight {T : Rel} (ht : IsTournament T) (hs : Tight T 4 Finset.univ)
    (e : V ≃ V) :
    IsTournament (fun x y => T (e x) (e y)) ∧
      Tight (fun x y => T (e x) (e y)) 4 Finset.univ := by
  refine ⟨⟨fun x => ht.1 _, fun x y h => ht.2 _ _ (e.injective.ne h)⟩, hs.size, ?_⟩
  rintro ⟨s, _, hn, htr⟩
  apply hs.avoid
  refine ⟨s.map e.toEmbedding, Finset.subset_univ _, by rwa [Finset.card_map], ?_⟩
  intro x hx y hy z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
  obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hz
  exact htr a ha b hb c hc

set_option maxRecDepth 16384 in
/-- With the four basis rows fixed, the rows at masks 4, 9 and 10 are incompatible. -/
private theorem incompatible :
    ∀ a ∈ candidates 4, ∀ b ∈ candidates 9, ∀ c ∈ candidates 10,
      let rs := (4, a) :: (9, b) :: (10, c) :: basisRows
      ¬ (oriented rs ∧ counts rs 4 Finset.univ) := by
  decide +kernel

private theorem hasChain_fifteen (T : Rel) (ht : IsTournament T) :
    HasChain T Finset.univ 5 := by
  by_contra hn
  have hs : Tight T 4 Finset.univ := ⟨by decide, hn⟩
  obtain ⟨e, he⟩ := labeling ht hs
  let U : Rel := fun x y => T (e x) (e y)
  obtain ⟨hu, hsu⟩ := relabel_tight ht hs e
  have hb : Records U basisRows := by
    intro r hr v
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    simpa using (he i v).symm
  let row := outs U Finset.univ
  have mem (x : V) : x ∉ labels → row x ∈ candidates x := fun hx =>
    row_mem hu hsu he hb hx
  let rs := (4, row 4) :: (9, row 9) :: (10, row 10) :: basisRows
  have hr : Records U rs := by
    intro r hmem
    simp only [rs, List.mem_cons] at hmem
    rcases hmem with rfl | rfl | rfl | hmem
    all_goals first | exact hb _ hmem | simp [row, outs]
  exact incompatible _ (mem 4 (by decide)) _ (mem 9 (by decide)) _ (mem 10 (by decide))
    ⟨oriented_of_records hu hr, counts_of_tight hu hr 4 _ hsu⟩

/--
**Erdős Problem 1216 is false.** It is not the case that $f(n) = \lfloor \log_2 n \rfloor + 1$ for
every $n \ge 1$, where $f(n)$ is the largest $m$ such that every tournament on $n$ vertices
contains a transitive subtournament on $m$ vertices.

Reid and Parker proved $f(n) \ge \lfloor \log_2 n + 4 - \log_2 7 \rfloor$ for all $n \ge 14$; at
$n = 14$ this gives $f(14) \ge 5 > 4 = \lfloor \log_2 14 \rfloor + 1$, while Stearns' bound
$f(n) \ge \lfloor \log_2 n \rfloor + 1$ holds for every $n \ge 1$.

Source: T. F. Bloom, Erdős Problems, Problem
#1216, https://www.erdosproblems.com/1216 (status DISPROVED); resolution: K. B. Reid and E. T.
Parker, Disproof of a conjecture of Erdős and Moser on tournaments, J. Combinatorial Theory 9
(1970), 225-238, erdosproblems.com/1216: f(n) ≥ ⌊log₂ n + 4 - log₂ 7⌋ for all n ≥ 14, so f(14) ≥ 5 >
⌊log₂ 14⌋ + 1.
-/
public theorem transitiveSubtournamentNumberEqLogTwo_refuted :
    ¬ transitiveSubtournamentNumberEqLogTwo := by
  intro h
  have h₅ : 5 ≤ transitiveSubtournamentNumber 15 := by
    apply le_csSup
    · refine ⟨15, ?_⟩
      intro m hm
      have ht : IsTournament (n := 15) (· < ·) :=
        ⟨lt_irrefl, fun x y hxy => by simp [lt_iff_le_and_ne, hxy, hxy.symm]⟩
      obtain ⟨s, rfl, _⟩ := hm (· < ·) ht
      simpa using s.card_le_univ
    · intro T ht
      obtain ⟨s, _, hc, htr⟩ := hasChain_fifteen T ht
      exact ⟨s, hc, htr⟩
  rw [h 15 (by decide)] at h₅
  exact (by decide : ¬ 5 ≤ Nat.log 2 15 + 1) h₅

end MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
