/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hamiltonicity of prisms over 3-connected planar graphs

The counterexample is the 26-copy chain from Špacapan's Figure 1. The three parts of
its verification are independent: a straight-line drawing, connectivity under two
vertex deletions, and a local obstruction to a spanning cycle in the prism.

For the obstruction, the four arms at the middle cut vertex of a clean copy exhaust
its four prism incidences. Each arm then also meets its outer terminal, or its sole
incidence at the cut vertex would be a bridge. The terminal pentagon between two
clean copies cannot carry the spanning cycle across: its two interior branches
force either two returns or incompatible layer changes. At least one window is
untouched by the eight possible hub incidences. Two consecutive pentagon cuts in
that window (one cut and the chain endpoint in the final window) trap vertices
away from the hubs.
-/

namespace Prism8339

abbrev V := Fin 991

/-- Label the lower half of `J` as in Fig. 1, with terminals 0 and 17. -/
def armEdges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (3, 5), (5, 6), (6, 7),
    (7, 8), (3, 8), (4, 17), (7, 17), (8, 17)]

def upperIndex (j : ℕ) : ℕ := if 0 < j ∧ j < 17 then j + 8 else j

def jEdges : List (ℕ × ℕ) :=
  armEdges ++ armEdges.map (fun (a, b) ↦ (upperIndex a, upperIndex b))

def hEdges : List (ℕ × ℕ) :=
  jEdges ++ jEdges.map (fun (a, b) ↦ (34 - b, 34 - a)) ++
    [(34, 35), (35, 38), (34, 36), (36, 37), (37, 38)]

def upper : List ℕ := [0, 9, 10, 11, 13, 14, 15, 17, 19, 20, 21, 23, 24, 25, 34, 35, 38]

def lower : List ℕ := [0, 1, 2, 3, 5, 6, 7, 17, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38]

/-- Adjacency tested in increasing order of the global labels. An edge of a copy is
charged to the copy containing its smaller endpoint (unless that endpoint is a hub). -/
def ascAdj (u v : ℕ) : Prop :=
  (u / 38 < 26 ∧ (u % 38, v - 38 * (u / 38)) ∈ hEdges) ∨
  (u ≤ 988 ∧ ((v = 989 ∧ u % 38 ∈ upper) ∨ (v = 990 ∧ u % 38 ∈ lower)))

instance (u v : ℕ) : Decidable (ascAdj u v) := inferInstanceAs (Decidable (_ ∨ _))

def graph : SimpleGraph V where
  Adj u v := (u.val < v.val ∧ ascAdj u.val v.val) ∨
    (v.val < u.val ∧ ascAdj v.val u.val)
  symm := ⟨fun _ _ ↦ Or.symm⟩
  loopless := ⟨fun _ h ↦ h.elim (fun h ↦ (Nat.lt_irrefl _ h.1))
    (fun h ↦ (Nat.lt_irrefl _ h.1))⟩

instance : DecidableRel graph.Adj := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

abbrev prism : SimpleGraph (V × Fin 2) := graph □ SimpleGraph.completeGraph (Fin 2)

/-- A vertex in the copy indexed by `i`. Consecutive copies share their terminal vertex. -/
def atCopy (i : Fin 26) (j : Fin 39) : V := ⟨38 * i.val + j.val, by omega⟩

@[simp] theorem val_atCopy (i : Fin 26) (j : Fin 39) :
    (atCopy i j).val = 38 * i.val + j.val := rfl

end Prism8339

open SimpleGraph

namespace Prism8339

/-- Each template edge has increasing labels in one 39-vertex copy. -/
theorem hEdges_bounds {e : ℕ × ℕ} (he : e ∈ hEdges) : e.1 < e.2 ∧ e.2 ≤ 38 := by
  have h : hEdges.all (fun p ↦ decide (p.1 < p.2 ∧ p.2 ≤ 38)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h _ he)

/-- Horizontal edges away from the hubs are precisely translated template edges. -/
theorem chain_adj_iff {u v : V} (hu : u.val < 989) (hv : v.val < 989) :
    graph.Adj u v ↔ ∃ i : Fin 26, ∃ e ∈ hEdges,
      (u.val = 38 * i.val + e.1 ∧ v.val = 38 * i.val + e.2) ∨
      (v.val = 38 * i.val + e.1 ∧ u.val = 38 * i.val + e.2) := by
  have asc (a b : V) (hb : b.val < 989) (hab : a.val < b.val) :
      ascAdj a.val b.val ↔ ∃ i : Fin 26, ∃ e ∈ hEdges,
        a.val = 38 * i.val + e.1 ∧ b.val = 38 * i.val + e.2 := by
    constructor
    · intro h
      rcases h with ⟨hi, he⟩ | ⟨_, hh⟩
      · refine ⟨⟨a.val / 38, hi⟩, _, he, ?_, ?_⟩ <;> dsimp <;> omega
      · rcases hh with h | h <;> omega
    · rintro ⟨i, e, he, ha, hb'⟩
      obtain ⟨h12, hbnd⟩ := hEdges_bounds he
      have hdiv : a.val / 38 = i.val := by omega
      have hmod : a.val % 38 = e.1 := by omega
      have hsub : b.val - 38 * i.val = e.2 := by omega
      exact Or.inl ⟨by simpa only [hdiv] using i.isLt, by simpa only [hdiv, hmod, hsub]⟩
  constructor
  · intro h
    rcases h with ⟨hlt, h⟩ | ⟨hlt, h⟩
    · obtain ⟨i, e, he, h'⟩ := (asc u v hv hlt).mp h
      exact ⟨i, e, he, Or.inl h'⟩
    · obtain ⟨i, e, he, h'⟩ := (asc v u hu hlt).mp h
      exact ⟨i, e, he, Or.inr h'⟩
  · rintro ⟨i, e, he, h | h⟩
    · have hh : u.val < v.val := by have := (hEdges_bounds he).1; omega
      exact Or.inl ⟨hh, (asc u v hv hh).mpr ⟨i, e, he, h⟩⟩
    · have hh : v.val < u.val := by have := (hEdges_bounds he).1; omega
      exact Or.inr ⟨hh, (asc v u hu hh).mpr ⟨i, e, he, h⟩⟩

abbrev P := V × Fin 2

/-- The four arms of `H`, ordered as the lower/upper branches of `J`, then
lower/upper branches of `L`. Label 0 is the outer port, away from the common cut at `b`. -/
def armLabel (f : Fin 4) (j : Fin 9) : Fin 39 :=
  ⟨let a := if f.val % 2 = 0 ∨ j.val = 0 then j.val else j.val + 8
    if f.val < 2 then a else 34 - a, by
      have := f.isLt
      have := j.isLt
      dsimp
      split_ifs <;> omega⟩

theorem armLabel_cast (f : Fin 4) (j : Fin 9) :
    0 < j.val → 0 < (armLabel f j).val ∧ (armLabel f j).val < 34 ∧
      (armLabel f j).val ≠ 17 := by decide +revert

theorem armLabel_inj : ∀ f : Fin 4, Function.Injective (armLabel f) := by
  intro f a b h
  have hf := f.isLt
  have ha := a.isLt
  have hb := b.isLt
  rw [Fin.ext_iff] at h ⊢
  simp only [armLabel] at h
  split_ifs at h <;> omega

theorem armLabel_disjoint (f g : Fin 4) (x y : Fin 9)
    (_hx : x.val ≠ 0) (hy : y.val ≠ 0) (h : armLabel f x = armLabel g y) : f = g := by
  have hf := f.isLt
  have hg := g.isLt
  have hxx := x.isLt
  have hyy := y.isLt
  rw [Fin.ext_iff] at h ⊢
  simp only [armLabel] at h
  split_ifs at h <;> omega

def copyEmbedding {n : ℕ} (i : Fin 26) (f : Fin n ↪ Fin 39) : (Fin n × Fin 2) ↪ P where
  toFun x := (atCopy i (f x.1), x.2)
  inj' := by
    intro x y h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    have he : f x.1 = f y.1 := by
      rw [Fin.ext_iff] at h₁ ⊢
      simp only [val_atCopy] at h₁
      omega
    exact Prod.ext (f.injective he) h₂

def armEmbedding (i : Fin 26) (f : Fin 4) : (Fin 9 × Fin 2) ↪ P :=
  copyEmbedding i ⟨armLabel f, armLabel_inj f⟩

def rightLabel (j : Fin 5) : Fin 39 := ⟨34 + j.val, by have := j.isLt; omega⟩

def rightEmbedding (i : Fin 26) : (Fin 5 × Fin 2) ↪ P :=
  copyEmbedding i ⟨rightLabel, fun _ _ h ↦ by
    rw [Fin.ext_iff] at h ⊢
    simp only [rightLabel] at h
    omega⟩

@[simp] theorem armEmbedding_val (i : Fin 26) (f : Fin 4) (p : Fin 9 × Fin 2) :
    ((armEmbedding i f) p).1.val = 38 * i.val + (armLabel f p.1).val := rfl

@[simp] theorem rightEmbedding_val (i : Fin 26) (p : Fin 5 × Fin 2) :
    ((rightEmbedding i) p).1.val = 38 * i.val + (34 + p.1.val) := rfl

@[simp] theorem armEmbedding_layer (i : Fin 26) (f : Fin 4) (p : Fin 9 × Fin 2) :
    ((armEmbedding i f) p).2 = p.2 := rfl

@[simp] theorem rightEmbedding_layer (i : Fin 26) (p : Fin 5 × Fin 2) :
    ((rightEmbedding i) p).2 = p.2 := rfl

end Prism8339

namespace PrismLocal

/-- The sum of weights of listed edges incident to a vertex. -/
def incidentWeight {V : Type*} [DecidableEq V] (w : V × V → ℕ) (edges : List (V × V))
    (v : V) : ℕ :=
  (edges.map fun e => if v = e.1 ∨ v = e.2 then w e else 0).sum

/-- The sum of weights of listed edges with exactly one endpoint in a cut. -/
def exitWeight {V : Type*} [DecidableEq V] (w : V × V → ℕ) (edges : List (V × V))
    (s : Finset V) : ℕ :=
  (edges.map fun e => if (e.1 ∈ s) ≠ (e.2 ∈ s) then w e else 0).sum

/-- A nonempty set of locally saturated vertices has a positive exit weight. -/
def NoTrap {V : Type*} [DecidableEq V] (w : V × V → ℕ) (edges : List (V × V)) : Prop :=
  ∀ s : Finset V, s.Nonempty → (∀ v ∈ s, incidentWeight w edges v = 2) →
    0 < exitWeight w edges s

/-- List both horizontal copies of each base edge, followed by the indicated rungs. -/
def prismEdges {n : ℕ} (base : List (Fin n × Fin n)) (rungs : List (Fin n)) :
    List ((Fin n × Fin 2) × (Fin n × Fin 2)) :=
  let horizontal (uv : Fin n × Fin n) : List ((Fin n × Fin 2) × (Fin n × Fin 2)) :=
    [((uv.1, 0), (uv.2, 0)), ((uv.1, 1), (uv.2, 1))]
  (base.flatMap horizontal) ++ (rungs.map fun v => ((v, (0 : Fin 2)), (v, 1)))

/-- One arm with its contacts at `b` omitted, as in the graph `Z` of Lemma 2.1. -/
def armEdges : List ((Fin 9 × Fin 2) × (Fin 9 × Fin 2)) :=
  prismEdges [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (3, 5), (5, 6), (6, 7), (7, 8), (3, 8)]
    [1, 2, 3, 4, 5, 6, 7, 8]

/-- The terminal block `R`; labels `0, 1, 2, 3, 4` are `c, 35, 36, 37, d`. -/
def rightEdges : List ((Fin 5 × Fin 2) × (Fin 5 × Fin 2)) :=
  prismEdges [(0, 1), (1, 4), (0, 2), (2, 3), (3, 4)] [1, 2, 3]

private theorem fin2_cases (t : Fin 2) : t = 0 ∨ t = 1 := by
  fin_cases t <;> decide

private def columns {n : ℕ} (xs : List (Fin n)) : Finset (Fin n × Fin 2) :=
  Finset.univ.filter fun u => u.1 ∈ xs

private theorem weight_bound_of_mem {V : Type*} (w : V → ℕ) (xs : List V) (x : V) (hx : x ∈ xs) :
    w x ≤ (xs.map w).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · simpa using Nat.le_trans (ih hx) (Nat.le_add_left _ _)

/-- A listed edge that crosses a cut contributes its full weight to the exit sum. -/
theorem edge_le_exitWeight {V : Type*} [DecidableEq V] (w : V × V → ℕ)
    (edges : List (V × V)) (s : Finset V) (e : V × V) (he : e ∈ edges)
    (hcross : (e.1 ∈ s) ≠ (e.2 ∈ s)) : w e ≤ exitWeight w edges s := by
  simpa [exitWeight, hcross] using
    weight_bound_of_mem (fun p : V × V => if (p.1 ∈ s) ≠ (p.2 ∈ s) then w p else 0) edges e he

private theorem arm_cut_positive (w : ((Fin 9 × Fin 2) × (Fin 9 × Fin 2)) → ℕ)
    (hdeg : ∀ v, v.1 ≠ 0 → incidentWeight w armEdges v = 2)
    (hno : NoTrap w armEdges) (s : Finset (Fin 9 × Fin 2)) (hs : s.Nonempty)
    (hzero : ∀ t, (0, t) ∈ s → incidentWeight w armEdges (0, t) = 2) :
    0 < exitWeight w armEdges s := by
  apply hno s hs
  rintro ⟨x, t⟩ hx
  by_cases hx0 : x = 0
  · subst x
    exact hzero t hx
  · exact hdeg (x, t) hx0

/-- Two positive even branch contact counts use at least four slots in total. If
at most four slots are available, both branches have exactly two contacts. -/
private theorem two_branch_contacts {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (haEven : a % 2 = 0) (hbEven : b % 2 = 0) (hab : a + b ≤ 4) : a = 2 ∧ b = 2 := by
  constructor <;> omega

/-- The possible distributions of a positive even count across two ports of
capacity two, once the three saturated-port cases have been excluded. -/
private theorem one_contact_per_port {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2)
    (hpos : 0 < a + b) (heven : (a + b) % 2 = 0)
    (h20 : ¬(a = 2 ∧ b = 0)) (h02 : ¬(b = 2 ∧ a = 0)) (h22 : ¬(a = 2 ∧ b = 2)) :
    a = 1 ∧ b = 1 := by
  constructor <;> omega

/-- At the shared vertex of the arm's pentagons, the two contacts leave no
room for the rung unless both ports are saturated. -/
private theorem one_contact_no_rung {a b r : ℕ} (ha : a + r ≤ 2) (hb : b + r ≤ 2)
    (hpos : 0 < a + b) (heven : (a + b) % 2 = 0)
    (h20 : ¬(a = 2 ∧ b = 0)) (h02 : ¬(b = 2 ∧ a = 0))
    (hfull : ¬(a + r = 2 ∧ b + r = 2)) : a = 1 ∧ b = 1 ∧ r = 0 := by
  have h22 : ¬(a = 2 ∧ b = 2) := by
    rintro ⟨ha', hb'⟩
    exact hfull ⟨by omega, by omega⟩
  obtain ⟨h₁, h₂⟩ := one_contact_per_port (by omega) (by omega) hpos heven h20 h02 h22
  exact ⟨h₁, h₂, by omega⟩

/-- The arm cannot be covered without a contact at `b` (Figure 1, Lemma 2.1).

The second pentagon forces exactly one edge at each copy of `x₃` toward the
first pentagon. The two branches of that pentagon then each have one edge at
`a` and one at `x₃`. The branch with two interior columns preserves the layer,
while the branch with one interior column switches it. -/
theorem arm_impossible (w : ((Fin 9 × Fin 2) × (Fin 9 × Fin 2)) → ℕ)
    (hsmall : ∀ e, w e ≤ 1) (hdeg : ∀ v, v.1 ≠ 0 → incidentWeight w armEdges v = 2)
    (hno : NoTrap w armEdges) : False := by
  let cut := arm_cut_positive w hdeg hno
  have h1₀ := hdeg (1, 0) (by decide)
  have h1₁ := hdeg (1, 1) (by decide)
  have h2₀ := hdeg (2, 0) (by decide)
  have h2₁ := hdeg (2, 1) (by decide)
  have h3₀ := hdeg (3, 0) (by decide)
  have h3₁ := hdeg (3, 1) (by decide)
  have h4₀ := hdeg (4, 0) (by decide)
  have h4₁ := hdeg (4, 1) (by decide)
  have h5₀ := hdeg (5, 0) (by decide)
  have h5₁ := hdeg (5, 1) (by decide)
  have h6₀ := hdeg (6, 0) (by decide)
  have h6₁ := hdeg (6, 1) (by decide)
  have h7₀ := hdeg (7, 0) (by decide)
  have h7₁ := hdeg (7, 1) (by decide)
  have h8₀ := hdeg (8, 0) (by decide)
  have h8₁ := hdeg (8, 1) (by decide)
  simp only [incidentWeight, Fin.isValue, armEdges, prismEdges, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil, Prod.mk.injEq,
    one_ne_zero, and_true, or_true, ↓reduceIte, zero_ne_one, and_self, and_false, or_self,
    Fin.reduceEq, or_false, List.sum_cons, List.sum_nil, add_zero, zero_add
    ] at h1₀ h1₁ h2₀ h2₁ h3₀ h3₁ h4₀ h4₁
  simp only [incidentWeight, Fin.isValue, armEdges, prismEdges, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil, Prod.mk.injEq,
    Fin.reduceEq, and_true, or_self, ↓reduceIte, zero_ne_one, and_self, or_true, and_false,
    or_false, List.sum_cons, List.sum_nil, add_zero, zero_add, one_ne_zero
    ] at h5₀ h5₁ h6₀ h6₁ h7₀ h7₁ h8₀ h8₁
  let c₀ := w ((3, 0), (5, 0)) + w ((3, 0), (8, 0))
  let c₁ := w ((3, 1), (5, 1)) + w ((3, 1), (8, 1))
  let r := w ((3, 0), (3, 1))
  have cPos := cut (columns [5, 6, 7, 8]) ⟨(5, 0), by decide⟩ (by simp [columns])
  simp only [exitWeight, columns, Fin.isValue, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, eq_iff_iff, ite_not, armEdges, prismEdges,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, Fin.reduceEq, or_self, ↓reduceIte, iff_true, or_true,
    List.sum_cons, List.sum_nil, add_zero, zero_add] at cPos
  have cEven : (c₀ + c₁) % 2 = 0 := by
    clear * - h5₀ h5₁ h6₀ h6₁ h7₀ h7₁ h8₀ h8₁
    omega
  have cBoth : c₀ = 1 ∧ c₁ = 1 ∧ r = 0 := by
    have h0 (h : c₀ = 2) (h' : c₁ = 0) : False := by
      have hc := cut (insert (3, 0) (columns [5, 6, 7, 8])) ⟨(5, 0), by decide⟩
        (by simp [columns])
      clear * - hc h h' h3₀
      simp [exitWeight, armEdges, prismEdges, columns] at hc
      omega
    have h1 (h : c₁ = 2) (h' : c₀ = 0) : False := by
      have hc := cut (insert (3, 1) (columns [5, 6, 7, 8])) ⟨(5, 0), by decide⟩
        (by simp [columns])
      clear * - hc h h' h3₁
      simp [exitWeight, armEdges, prismEdges, columns] at hc
      omega
    have hFull (h : c₀ + r = 2) (h' : c₁ + r = 2) : False := by
      have hc := cut (columns [3, 5, 6, 7, 8]) ⟨(5, 0), by decide⟩ (by simp [columns])
      clear * - hc h h' h3₀ h3₁
      simp [exitWeight, armEdges, prismEdges, columns] at hc
      omega
    apply one_contact_no_rung (a := c₀) (b := c₁) (r := r) _ _ _ cEven
      (fun h ↦ h0 h.1 h.2) (fun h ↦ h1 h.1 h.2) (fun h ↦ hFull h.1 h.2)
    · clear * - h3₀
      omega
    · clear * - h3₁
      omega
    · clear * - cPos
      omega
  obtain ⟨c₀one, c₁one, rZero⟩ := cBoth
  let a₀ := incidentWeight w armEdges (0, 0)
  let a₁ := incidentWeight w armEdges (0, 1)
  have ea₀ : a₀ = w ((0, 0), (1, 0)) + w ((0, 0), (4, 0)) := by
    simp [a₀, incidentWeight, armEdges, prismEdges]
  have ea₁ : a₁ = w ((0, 1), (1, 1)) + w ((0, 1), (4, 1)) := by
    simp [a₁, incidentWeight, armEdges, prismEdges]
  have aMax₀ : a₀ ≤ 2 := by
    have h1 := hsmall ((0, 0), (1, 0))
    have h4 := hsmall ((0, 0), (4, 0))
    rw [ea₀]
    exact Nat.add_le_add h1 h4
  have aMax₁ : a₁ ≤ 2 := by
    have h1 := hsmall ((0, 1), (1, 1))
    have h4 := hsmall ((0, 1), (4, 1))
    rw [ea₁]
    exact Nat.add_le_add h1 h4
  have aEven : (a₀ + a₁) % 2 = 0 := by
    clear * - ea₀ ea₁ c₀one c₁one rZero h1₀ h1₁ h2₀ h2₁ h3₀ h3₁ h4₀ h4₁
    omega
  have aBoth : a₀ = 1 ∧ a₁ = 1 := by
    have ha₀ (h : a₀ = 2) (h' : a₁ = 0) : False := by
      have hc := cut (insert (0, 0) (columns [1, 2, 3, 4, 5, 6, 7, 8])) ⟨(1, 0), by decide⟩
        (by
          intro t ht
          have ht0 : t = 0 := by simpa [columns] using ht
          subst t
          exact h)
      clear * - hc h' ea₁
      simp [exitWeight, armEdges, prismEdges, columns] at hc
      omega
    have ha₁ (h : a₁ = 2) (h' : a₀ = 0) : False := by
      have hc := cut (insert (0, 1) (columns [1, 2, 3, 4, 5, 6, 7, 8])) ⟨(1, 0), by decide⟩
        (by
          intro t ht
          have ht1 : t = 1 := by simpa [columns] using ht
          subst t
          exact h)
      clear * - hc h' ea₀
      simp [exitWeight, armEdges, prismEdges, columns] at hc
      omega
    have ha₂ (h : a₀ = 2) (h' : a₁ = 2) : False := by
      have hc := cut (columns [0, 1, 2, 3, 4, 5, 6, 7, 8]) ⟨(1, 0), by decide⟩
        (by
          intro t _
          rcases fin2_cases t with rfl | rfl
          · exact h
          · exact h')
      simp [exitWeight, armEdges, prismEdges, columns] at hc
    have aPos := cut (columns [1, 2, 3, 4, 5, 6, 7, 8]) ⟨(1, 0), by decide⟩
      (by simp [columns])
    simp only [exitWeight, columns, Fin.isValue, List.mem_cons, List.not_mem_nil, or_false,
      Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, eq_iff_iff, ite_not, armEdges,
      prismEdges, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil, zero_ne_one, Fin.reduceEq, or_self, iff_true,
      ↓reduceIte, or_true, List.sum_cons, List.sum_nil, add_zero, zero_add] at aPos
    apply one_contact_per_port aMax₀ aMax₁ _ aEven
      (fun h ↦ ha₀ h.1 h.2) (fun h ↦ ha₁ h.1 h.2) (fun h ↦ ha₂ h.1 h.2)
    clear * - aPos ea₀ ea₁
    omega
  obtain ⟨a₀one, a₁one⟩ := aBoth
  let longA := w ((0, 0), (1, 0)) + w ((0, 1), (1, 1))
  let longX := w ((2, 0), (3, 0)) + w ((2, 1), (3, 1))
  let shortA := w ((0, 0), (4, 0)) + w ((0, 1), (4, 1))
  let shortX := w ((3, 0), (4, 0)) + w ((3, 1), (4, 1))
  have longPos := cut (columns [1, 2]) ⟨(1, 0), by decide⟩ (by simp [columns])
  have shortPos := cut (columns [4]) ⟨(4, 0), by decide⟩ (by simp [columns])
  simp only [exitWeight, columns, Fin.isValue, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, eq_iff_iff, ite_not, armEdges, prismEdges,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, zero_ne_one, Fin.reduceEq, or_self, iff_true, ↓reduceIte, or_true,
    iff_false, not_true_eq_false, List.sum_cons, List.sum_nil, add_zero, zero_add
    ] at longPos shortPos
  have longEven : (longA + longX) % 2 = 0 := by
    clear * - h1₀ h1₁ h2₀ h2₁
    omega
  have shortEven : (shortA + shortX) % 2 = 0 := by
    clear * - h4₀ h4₁
    omega
  have atA : longA + shortA = 2 := by
    clear * - ea₀ ea₁ a₀one a₁one
    omega
  have atX : longX + shortX = 2 := by
    clear * - h3₀ h3₁ c₀one c₁one rZero
    omega
  obtain ⟨longTwo, shortTwo⟩ := two_branch_contacts
    (a := longA + longX) (b := shortA + shortX)
    (by clear * - longPos; omega) (by clear * - shortPos; omega)
    longEven shortEven (by clear * - atA atX; omega)
  have longAone : longA = 1 := by
    have ha₀ (h : longA = 0) : False := by
      have hc := cut (columns [1, 2, 3, 5, 6, 7, 8]) ⟨(1, 0), by decide⟩ (by simp [columns])
      clear * - hc h longTwo shortTwo atA
      simp [exitWeight, armEdges, prismEdges, columns] at hc
      omega
    have ha₂ (h : longA = 2) : False := by
      have hc := cut (columns [3, 4, 5, 6, 7, 8]) ⟨(3, 0), by decide⟩ (by simp [columns])
      clear * - hc h longTwo atA
      simp [exitWeight, armEdges, prismEdges, columns] at hc
      omega
    have h0 : longA ≠ 0 := ha₀
    have h2 : longA ≠ 2 := ha₂
    clear * - h0 h2 longTwo
    omega
  clear * - longAone longTwo shortTwo atA h1₀ h1₁ h2₀ h2₁ h4₀ h4₁ ea₀ a₀one h3₀ c₀one rZero
  omega

private theorem right_cut_positive (w : ((Fin 5 × Fin 2) × (Fin 5 × Fin 2)) → ℕ)
    (hdeg : ∀ v, v.1 ≠ 0 → v.1 ≠ 4 → incidentWeight w rightEdges v = 2)
    (hno : NoTrap w rightEdges) (s : Finset (Fin 5 × Fin 2)) (hs : s.Nonempty)
    (h0 : ∀ t, (0, t) ∉ s) (h4 : ∀ t, (4, t) ∉ s) : 0 < exitWeight w rightEdges s := by
  apply hno s hs
  rintro ⟨x, t⟩ hx
  exact hdeg (x, t) (by rintro rfl; exact h0 t hx) (by rintro rfl; exact h4 t hx)

/-- The terminal block separates all ports that are available for outside edges.

Each of the two interior branches has exactly two contacts. If both branches
have contacts at both ends, the short branch switches layers and the long one
preserves them. Therefore some terminal has both contacts at the same port;
that port has no remaining capacity for an outside edge. -/
theorem right_cut (w : ((Fin 5 × Fin 2) × (Fin 5 × Fin 2)) → ℕ)
    (hdeg : ∀ v, v.1 ≠ 0 → v.1 ≠ 4 → incidentWeight w rightEdges v = 2)
    (hl : incidentWeight w rightEdges (0, 0) + incidentWeight w rightEdges (0, 1) ≤ 2)
    (hr : incidentWeight w rightEdges (4, 0) + incidentWeight w rightEdges (4, 1) ≤ 2)
    (hno : NoTrap w rightEdges) :
    ∃ s : Finset (Fin 5 × Fin 2), exitWeight w rightEdges s = 0 ∧
      (∀ t, incidentWeight w rightEdges (0, t) < 2 → (0, t) ∈ s) ∧
      (∀ t, incidentWeight w rightEdges (4, t) < 2 → (4, t) ∉ s) := by
  let cut := right_cut_positive w hdeg hno
  have h1₀ := hdeg (1, 0) (by decide) (by decide)
  have h1₁ := hdeg (1, 1) (by decide) (by decide)
  have h2₀ := hdeg (2, 0) (by decide) (by decide)
  have h2₁ := hdeg (2, 1) (by decide) (by decide)
  have h3₀ := hdeg (3, 0) (by decide) (by decide)
  have h3₁ := hdeg (3, 1) (by decide) (by decide)
  have shortPos := cut (columns [1]) ⟨(1, 0), by decide⟩ (by simp [columns]) (by simp [columns])
  have longPos := cut (columns [2, 3]) ⟨(2, 0), by decide⟩ (by simp [columns]) (by simp [columns])
  simp only [incidentWeight, Fin.isValue, rightEdges, prismEdges, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, Prod.mk.injEq, one_ne_zero, and_true, or_true, ↓reduceIte, zero_ne_one, and_self,
    and_false, or_self, Fin.reduceEq, or_false, List.sum_cons, List.sum_nil, add_zero, zero_add
    ] at h1₀ h1₁ h2₀ h2₁ h3₀ h3₁ hl hr
  simp only [exitWeight, columns, Fin.isValue, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, eq_iff_iff, ite_not, rightEdges,
    prismEdges, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, zero_ne_one, iff_true, ↓reduceIte, Fin.reduceEq,
    iff_false, not_true_eq_false, List.sum_cons, List.sum_nil, add_zero, or_self, or_true, zero_add
    ] at shortPos longPos
  let shortLeft := w ((0, 0), (1, 0)) + w ((0, 1), (1, 1))
  let shortRight := w ((1, 0), (4, 0)) + w ((1, 1), (4, 1))
  let longLeft := w ((0, 0), (2, 0)) + w ((0, 1), (2, 1))
  let longRight := w ((3, 0), (4, 0)) + w ((3, 1), (4, 1))
  have shortEven : (shortLeft + shortRight) % 2 = 0 := by
    clear * - h1₀ h1₁
    omega
  have longEven : (longLeft + longRight) % 2 = 0 := by
    clear * - h2₀ h2₁ h3₀ h3₁
    omega
  obtain ⟨shortTwo, longTwo⟩ := two_branch_contacts
    (a := shortLeft + shortRight) (b := longLeft + longRight)
    (by clear * - shortPos; omega) (by clear * - longPos; omega)
    shortEven longEven (by clear * - hl hr; omega)
  by_cases h0 : shortLeft = 0
  · refine ⟨columns [0, 2, 3], ?_, by simp [columns], by simp [columns]⟩
    clear * - h0 shortTwo longTwo hl hr
    simp [exitWeight, rightEdges, prismEdges, columns]
    omega
  by_cases h2 : shortLeft = 2
  · refine ⟨columns [0, 1], ?_, by simp [columns], by simp [columns]⟩
    clear * - h2 shortTwo longTwo hl hr
    simp [exitWeight, rightEdges, prismEdges, columns]
    omega
  have hLeftOne : shortLeft = 1 := by
    clear * - h0 h2 shortTwo
    omega
  have hRightOne : shortRight = 1 := by
    clear * - hLeftOne shortTwo
    omega
  have hLongLeftOne : longLeft = 1 := by
    clear * - hl hr longTwo hLeftOne hRightOne
    omega
  have hLongRightOne : longRight = 1 := by
    clear * - hLongLeftOne longTwo
    omega
  have switches : w ((0, 0), (1, 0)) + w ((1, 0), (4, 0)) = 1 := by
    clear * - h1₀ h1₁ hLeftOne hRightOne
    omega
  have preserves : w ((0, 0), (2, 0)) = w ((3, 0), (4, 0)) := by
    clear * - h2₀ h2₁ h3₀ h3₁ hLongLeftOne hLongRightOne
    omega
  have hShared :
      incidentWeight w rightEdges (0, 0) = 2 ∨ incidentWeight w rightEdges (0, 1) = 2 ∨
      incidentWeight w rightEdges (4, 0) = 2 ∨ incidentWeight w rightEdges (4, 1) = 2 := by
    clear * - hLeftOne hRightOne hLongLeftOne hLongRightOne switches preserves
    simp [incidentWeight, rightEdges, prismEdges]
    omega
  have eqL₀ : incidentWeight w rightEdges (0, 0) =
      w ((0, 0), (1, 0)) + w ((0, 0), (2, 0)) := by
    simp [incidentWeight, rightEdges, prismEdges]
  have eqL₁ : incidentWeight w rightEdges (0, 1) =
      w ((0, 1), (1, 1)) + w ((0, 1), (2, 1)) := by
    simp [incidentWeight, rightEdges, prismEdges]
  have eqR₀ : incidentWeight w rightEdges (4, 0) =
      w ((1, 0), (4, 0)) + w ((3, 0), (4, 0)) := by
    simp [incidentWeight, rightEdges, prismEdges]
  have eqR₁ : incidentWeight w rightEdges (4, 1) =
      w ((1, 1), (4, 1)) + w ((3, 1), (4, 1)) := by
    simp [incidentWeight, rightEdges, prismEdges]
  rcases hShared with hL₀ | hL₁ | hR₀ | hR₁
  · refine ⟨{(0, 1)}, ?_, ?_, by simp⟩
    · clear * - hL₀ eqL₀ hl
      simp [exitWeight, rightEdges, prismEdges]
      omega
    · intro t ht
      rcases fin2_cases t with rfl | rfl
      · exact (Nat.ne_of_lt ht hL₀).elim
      · decide
  · refine ⟨{(0, 0)}, ?_, ?_, by simp⟩
    · clear * - hL₁ eqL₁ hl
      simp [exitWeight, rightEdges, prismEdges]
      omega
    · intro t ht
      rcases fin2_cases t with rfl | rfl
      · decide
      · exact (Nat.ne_of_lt ht hL₁).elim
  · refine ⟨insert (4, 0) (columns [0, 1, 2, 3]), ?_, by simp [columns], ?_⟩
    · clear * - hR₀ eqR₀ hr
      simp [exitWeight, rightEdges, prismEdges, columns]
      omega
    · intro t ht
      rcases fin2_cases t with rfl | rfl
      · exact (Nat.ne_of_lt ht hR₀).elim
      · decide
  · refine ⟨insert (4, 1) (columns [0, 1, 2, 3]), ?_, by simp [columns], ?_⟩
    · clear * - hR₁ eqR₁ hr
      simp [exitWeight, rightEdges, prismEdges, columns]
      omega
    · intro t ht
      rcases fin2_cases t with rfl | rfl
      · decide
      · exact (Nat.ne_of_lt ht hR₁).elim

/-- A Boolean form of `right_cut`, with `false` on the left and `true` on the right. -/
theorem right_coloring (w : ((Fin 5 × Fin 2) × (Fin 5 × Fin 2)) → ℕ)
    (hdeg : ∀ v, v.1 ≠ 0 → v.1 ≠ 4 → incidentWeight w rightEdges v = 2)
    (hl : incidentWeight w rightEdges (0, 0) + incidentWeight w rightEdges (0, 1) ≤ 2)
    (hr : incidentWeight w rightEdges (4, 0) + incidentWeight w rightEdges (4, 1) ≤ 2)
    (hno : NoTrap w rightEdges) :
    ∃ f : Fin 5 × Fin 2 → Bool, (∀ e ∈ rightEdges, 0 < w e → f e.1 = f e.2) ∧
      (∀ t, incidentWeight w rightEdges (0, t) < 2 → f (0, t) = false) ∧
      (∀ t, incidentWeight w rightEdges (4, t) < 2 → f (4, t) = true) := by
  obtain ⟨s, hs, hleft, hright⟩ := right_cut w hdeg hl hr hno
  refine ⟨fun v => decide (v ∉ s), ?_, ?_, ?_⟩
  · intro e he hw
    have hmem : (e.1 ∈ s) = (e.2 ∈ s) := by
      by_contra hc
      have hbound := edge_le_exitWeight w rightEdges s e he hc
      omega
    by_cases hleftMem : e.1 ∈ s
    · have hrightMem : e.2 ∈ s := (Iff.of_eq hmem).mp hleftMem
      simp [hleftMem, hrightMem]
    · have hrightMem : e.2 ∉ s := fun he2 => hleftMem ((Iff.of_eq hmem).mpr he2)
      simp [hleftMem, hrightMem]
  · intro t ht
    simp [hleft t ht]
  · intro t ht
    simp [hright t ht]
end PrismLocal

namespace PrismLocal

variable {L P : Type*} [DecidableEq L]

/-- List the other endpoints of the listed edges incident to `u`. -/
def localNbr (edges : List (L × L)) (u : L) : List L :=
  edges.filterMap fun ab ↦ if ab.1 = u then some ab.2 else if ab.2 = u then some ab.1 else none

theorem mem_localNbr_iff {edges : List (L × L)} {u v : L} :
    v ∈ localNbr edges u ↔ (u, v) ∈ edges ∨ (v, u) ∈ edges := by
  unfold localNbr
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, h⟩
    dsimp only at h
    split at h
    · rename_i ha
      exact Or.inl (ha ▸ Option.some.inj h ▸ hmem)
    · split at h
      · rename_i hb
        exact Or.inr (hb ▸ Option.some.inj h ▸ hmem)
      · cases h
  · rintro (h | h)
    · exact ⟨(u, v), h, by simp⟩
    · refine ⟨(v, u), h, ?_⟩
      by_cases he : v = u <;> simp [he]

variable (C : SimpleGraph P) [DecidableRel C.Adj] (e : L ↪ P)

/-- A listed edge contributes one exactly when its image belongs to `C`. -/
def cycleWeight (ab : L × L) : ℕ := if C.Adj (e ab.1) (e ab.2) then 1 else 0

/-- Images of the listed neighbors that are adjacent in `C`. -/
def selectedNbr (edges : List (L × L)) (u : L) : Finset P :=
  (((localNbr edges u).filter fun v ↦ decide (C.Adj (e u) (e v))).toFinset).map e

theorem mem_selectedNbr_iff {edges : List (L × L)} {u : L} {v : P} :
    v ∈ selectedNbr C e edges u ↔ C.Adj (e u) v ∧ ∃ x ∈ localNbr edges u, e x = v := by
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨hmem, hadj⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
    exact ⟨of_decide_eq_true hadj, x, hmem, rfl⟩
  · rintro ⟨hadj, x, hx, rfl⟩
    exact Finset.mem_map.mpr ⟨x, List.mem_toFinset.mpr (List.mem_filter.mpr
      ⟨hx, decide_eq_true hadj⟩), rfl⟩

private theorem incidentWeight_eq_length_selected (edges : List (L × L)) (u : L) :
    incidentWeight (cycleWeight C e) edges u =
      ((localNbr edges u).filter fun v ↦ decide (C.Adj (e u) (e v))).length := by
  induction edges with
  | nil => rfl
  | cons ab edges ih =>
    obtain ⟨a, b⟩ := ab
    by_cases ha : a = u
    · subst a
      by_cases hadj : C.Adj (e u) (e b) <;>
        simp [incidentWeight, localNbr, cycleWeight, hadj] at ih ⊢ <;> omega
    · by_cases hb : b = u
      · subst b
        have hsymm : C.Adj (e a) (e u) ↔ C.Adj (e u) (e a) := ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
        by_cases hadj : C.Adj (e u) (e a) <;>
          simp [incidentWeight, localNbr, cycleWeight, ha, Ne.symm ha, hsymm, hadj] at ih ⊢ <;>
          omega
      · simpa [incidentWeight, localNbr, cycleWeight, ha, hb, Ne.symm ha, Ne.symm hb] using ih

theorem incidentWeight_eq_card_selectedNbr (edges : List (L × L)) (u : L)
    (hnodup : (localNbr edges u).Nodup) :
    incidentWeight (cycleWeight C e) edges u = (selectedNbr C e edges u).card := by
  rw [selectedNbr, Finset.card_map, List.toFinset_card_of_nodup (hnodup.filter _)]
  exact incidentWeight_eq_length_selected C e edges u

section Degree

variable [Fintype P]

theorem selectedNbr_subset_neighborFinset (edges : List (L × L)) (u : L) :
    selectedNbr C e edges u ⊆ C.neighborFinset (e u) := by
  intro v hv
  exact (C.mem_neighborFinset _ _).mpr ((mem_selectedNbr_iff C e).mp hv).1

theorem incidentWeight_le_two (edges : List (L × L)) (u : L)
    (hnodup : (localNbr edges u).Nodup) (hdeg : C.degree (e u) = 2) :
    incidentWeight (cycleWeight C e) edges u ≤ 2 := by
  rw [incidentWeight_eq_card_selectedNbr C e edges u hnodup, ← hdeg,
    ← C.card_neighborFinset_eq_degree]
  exact Finset.card_le_card (selectedNbr_subset_neighborFinset C e edges u)

theorem incidentWeight_eq_two (edges : List (L × L)) (u : L)
    (hnodup : (localNbr edges u).Nodup) (hdeg : C.degree (e u) = 2)
    (hcover : ∀ v, C.Adj (e u) v → ∃ x ∈ localNbr edges u, e x = v) :
    incidentWeight (cycleWeight C e) edges u = 2 := by
  have heq : selectedNbr C e edges u = C.neighborFinset (e u) := by
    apply Finset.Subset.antisymm (selectedNbr_subset_neighborFinset C e edges u)
    intro v hv
    have hadj := (C.mem_neighborFinset _ _).mp hv
    exact (mem_selectedNbr_iff C e).mpr ⟨hadj, hcover v hadj⟩
  rw [incidentWeight_eq_card_selectedNbr C e edges u hnodup, heq,
    C.card_neighborFinset_eq_degree, hdeg]

theorem neighbor_represented_of_incidentWeight_eq_two (edges : List (L × L)) (u : L)
    (hnodup : (localNbr edges u).Nodup) (hdeg : C.degree (e u) = 2)
    (hweight : incidentWeight (cycleWeight C e) edges u = 2)
    {v : P} (hadj : C.Adj (e u) v) : ∃ x ∈ localNbr edges u, e x = v := by
  have heq : selectedNbr C e edges u = C.neighborFinset (e u) := by
    apply Finset.eq_of_subset_of_card_le (selectedNbr_subset_neighborFinset C e edges u)
    rw [C.card_neighborFinset_eq_degree, hdeg,
      ← incidentWeight_eq_card_selectedNbr C e edges u hnodup, hweight]
  have hv : v ∈ selectedNbr C e edges u := heq.symm ▸ (C.mem_neighborFinset _ _).mpr hadj
  exact ((mem_selectedNbr_iff C e).mp hv).2

end Degree

/-- A cut separating two vertices in a connected graph has a crossing edge. -/
theorem exists_edge_across {X : Type*} {G : SimpleGraph X} (hc : G.Connected)
    {s : Set X} {u v : X} (hu : u ∈ s) (hv : v ∉ s) :
    ∃ a ∈ s, ∃ b ∉ s, G.Adj a b := by
  obtain ⟨p⟩ := hc.preconnected u v
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
    by_cases hw : w ∈ s
    · exact ih hw hv
    · exact ⟨u, hu, w, hw, huw⟩

private theorem sum_pos_of_pos_mem {xs : List ℕ} {n : ℕ} (hn : 0 < n) (hm : n ∈ xs) :
    0 < xs.sum := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp hm with rfl | h
    · omega
    · have := ih h
      omega

private theorem exitWeight_pos_of_adj_of_mem {edges : List (L × L)} {s : Finset L}
    {ab : L × L} (hab : ab ∈ edges) (hcut : (ab.1 ∈ s) ≠ (ab.2 ∈ s))
    (hadj : C.Adj (e ab.1) (e ab.2)) : 0 < exitWeight (cycleWeight C e) edges s := by
  unfold exitWeight
  apply sum_pos_of_pos_mem (n := 1) (by decide)
  exact List.mem_map.mpr ⟨ab, hab, by simp [hcut, cycleWeight, hadj]⟩

/-- Restricting a connected 2-regular graph to the listed edges cannot create a trap. -/
theorem noTrap_cycleWeight [Fintype P] (edges : List (L × L))
    (hnodup : ∀ u, (localNbr edges u).Nodup) (hdeg : ∀ p, C.degree p = 2)
    (hc : C.Connected) (hout : ∃ p, p ∉ Set.range e) : NoTrap (cycleWeight C e) edges := by
  intro s hs hweight
  let t : Set P := ↑(s.map e)
  obtain ⟨x, hx⟩ := hs
  obtain ⟨p, hp⟩ := hout
  have hx' : e x ∈ t := Finset.mem_map.mpr ⟨x, hx, rfl⟩
  have hp' : p ∉ t := by
    intro hm
    obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hm
    exact hp ⟨v, hv⟩
  obtain ⟨a, ha, b, hb, hab⟩ := exists_edge_across hc hx' hp'
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨v, hv, rfl⟩ := neighbor_represented_of_incidentWeight_eq_two C e edges u
    (hnodup u) (hdeg (e u)) (hweight u hu) hab
  have hv' : v ∉ s := fun hm ↦ hb (Finset.mem_map.mpr ⟨v, hm, rfl⟩)
  have hcut : (u ∈ s) ≠ (v ∈ s) := fun he ↦ hv' (he ▸ hu)
  rcases mem_localNbr_iff.mp hv with h | h
  · exact exitWeight_pos_of_adj_of_mem C e h hcut hab
  · exact exitWeight_pos_of_adj_of_mem C e h hcut.symm hab.symm

end PrismLocal

open SimpleGraph PrismLocal

namespace Prism8339

private def armListed (p q : Fin 9 × Fin 2) : Bool :=
  PrismLocal.armEdges.contains (p, q) || PrismLocal.armEdges.contains (q, p)

@[simp] private theorem armListed_iff (p q : Fin 9 × Fin 2) :
    armListed p q = true ↔ q ∈ localNbr PrismLocal.armEdges p := by
  simp [armListed, mem_localNbr_iff]

private def armCheck (f : Fin 4) (p : Fin 9 × Fin 2) (a b : ℕ) : Bool :=
  (a != (armLabel f p.1).val) || (b == 17) ||
    (List.finRange 9).any (fun j ↦ (b == (armLabel f j).val) && armListed p (j, p.2))

private theorem armCheck_iff (f : Fin 4) (p : Fin 9 × Fin 2) (a b : ℕ) :
    armCheck f p a b = true ↔
      a = (armLabel f p.1).val → b = 17 ∨ ∃ j : Fin 9,
        b = (armLabel f j).val ∧ (j, p.2) ∈ localNbr PrismLocal.armEdges p := by
  simp [armCheck, List.any_eq_true, imp_iff_not_or, or_assoc]

private def armTemplateOK : Prop :=
  ∀ (f : Fin 4) (p : Fin 9 × Fin 2), p.1 ≠ 0 →
    hEdges.all (fun ab ↦ armCheck f p ab.1 ab.2 && armCheck f p ab.2 ab.1) = true

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
-- The table checks both orientations of every template edge for each interior port.
private theorem armTemplateCheck : armTemplateOK := by
  unfold armTemplateOK
  decide +kernel

private theorem armRung (p : Fin 9 × Fin 2) (l : Fin 2) (hp : p.1 ≠ 0) (hl : p.2 ≠ l) :
    (p.1, l) ∈ localNbr PrismLocal.armEdges p := by
  rw [← armListed_iff]
  exact (by decide +kernel : ∀ (p : Fin 9 × Fin 2) (l : Fin 2),
    p.1 ≠ 0 → p.2 ≠ l → armListed p (p.1, l) = true) p l hp hl

theorem arm_neighbors (i : Fin 26) (f : Fin 4) (p : Fin 9 × Fin 2) (q : P)
    (hp : p.1 ≠ 0) (hq : q.1.val < 989) (ha : prism.Adj (armEmbedding i f p) q) :
    q = (atCopy i 17, p.2) ∨ ∃ r, r ∈ localNbr PrismLocal.armEdges p ∧ armEmbedding i f r = q := by
  let x := armEmbedding i f p
  have gx : x.1.val = 38 * i.val + (armLabel f p.1).val := rfl
  have lx : x.2 = p.2 := rfl
  have hx : 0 < p.1.val := Nat.pos_of_ne_zero fun h ↦ hp (Fin.ext h)
  obtain ⟨hpos, hhigh, _⟩ := armLabel_cast f p.1 hx
  have hix := i.isLt
  have hsmall : x.1.val < 989 := by omega
  rcases boxProd_adj.mp ha with ⟨horiz, hL⟩ | ⟨vert, hv⟩
  · change graph.Adj x.1 q.1 at horiz
    change x.2 = q.2 at hL
    obtain ⟨i', ab, hab, hpair⟩ := (chain_adj_iff hsmall hq).mp horiz
    obtain ⟨hord, hbound⟩ := hEdges_bounds hab
    have hi' : i' = i := by
      apply Fin.ext
      rcases hpair with h | h <;> omega
    subst i'
    have hcheck : armCheck f p ab.1 ab.2 = true ∧ armCheck f p ab.2 ab.1 = true := by
      simpa using List.all_eq_true.mp (armTemplateCheck f p hp) ab hab
    have result (a : ℕ) (ha' : q.1.val = 38 * i.val + a)
        (hh : a = 17 ∨ ∃ j : Fin 9, a = (armLabel f j).val ∧
          (j, p.2) ∈ localNbr PrismLocal.armEdges p) :
        q = (atCopy i 17, p.2) ∨
          ∃ r, r ∈ localNbr PrismLocal.armEdges p ∧ armEmbedding i f r = q := by
      rcases hh with h | ⟨j, hj, he⟩
      · left
        apply Prod.ext
        · apply Fin.ext; simp only [val_atCopy]; omega
        · exact hL.symm.trans lx
      · right
        refine ⟨(j, p.2), he, ?_⟩
        apply Prod.ext
        · apply Fin.ext; simp only [armEmbedding_val]; omega
        · exact lx.symm.trans hL
    rcases hpair with h | h
    · exact result ab.2 h.2 ((armCheck_iff f p _ _).mp hcheck.1 (by omega))
    · exact result ab.1 h.1 ((armCheck_iff f p _ _).mp hcheck.2 (by omega))
  · have hl : p.2 ≠ q.2 := fun h ↦ vert.ne (lx.trans h)
    right
    refine ⟨(p.1, q.2), armRung p q.2 hp hl, ?_⟩
    exact Prod.ext hv rfl

theorem armNbr_nodup (p : Fin 9 × Fin 2) : (localNbr PrismLocal.armEdges p).Nodup := by
  decide +revert +kernel

theorem armEmbedding_is_inside (i : Fin 26) (f : Fin 4) {p : Fin 9 × Fin 2}
    (hp : p.1 ≠ 0) :
    38 * i.val < (armEmbedding i f p).1.val ∧ (armEmbedding i f p).1.val < 38 * i.val + 34 := by
  have hx : 0 < p.1.val := Nat.pos_of_ne_zero fun h ↦ hp (Fin.ext h)
  have := armLabel_cast f p.1 hx
  simp only [armEmbedding_val]
  omega

theorem arm_port (f : Fin 4) : (armLabel f 0).val = if f.val < 2 then 0 else 34 := by
  simp [armLabel]

end Prism8339

open SimpleGraph
open scoped BigOperators

namespace Prism8339

local notation "P" => V × Fin 2

theorem exists_cycle_subgraph (h : prism.IsHamiltonian) :
    ∃ C : SimpleGraph P,
      C ≤ prism ∧ C.IsHamiltonian ∧ C.Connected ∧ ∀ v, (C.neighborSet v).ncard = 2 := by
  classical
  let n := 1982
  have hcard : Fintype.card P = n := by simp [n, V]
  obtain ⟨f⟩ := (isHamiltonian_iff_cycleGraph_isContained
    (by omega : 3 ≤ Fintype.card P)).mp h
  rw [hcard] at f
  let e : Fin n ≃ P := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨f.injective, by simpa using hcard.symm⟩)
  let C : SimpleGraph P := (cycleGraph n).map e.toEmbedding
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj e.toEmbedding _ _ _).mp hxy
    exact f.toHom.map_adj huv
  · apply (isHamiltonian_iff_cycleGraph_isContained (by omega : 3 ≤ Fintype.card P)).mpr
    rw [hcard]
    let iso := SimpleGraph.Iso.map e (cycleGraph n)
    exact ⟨⟨⟨e, fun hxy ↦ iso.map_adj_iff.mpr hxy⟩, e.injective⟩⟩
  · exact (SimpleGraph.Iso.map e (cycleGraph n)).connected_iff.mp
      (connected_cycleGraph_add_one (n := 1981))
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    change ((cycleGraph n).map e.toEmbedding |>.neighborSet (e.toEmbedding u)).ncard = 2
    rw [neighborSet_map]
    rw [Set.ncard_image_of_injective _ e.toEmbedding.injective, ncard_neighborSet]
    exact cycleGraph_degree_three_le (n := 1979) (v := u)

private def window (v : P) : Fin 9 := ⟨v.1.val / 114, by have := v.1.isLt; omega⟩

private def hubs : Finset P := {(989, 0), (989, 1), (990, 0), (990, 1)}

private theorem mem_hubs {v : P} : v ∈ hubs ↔ 989 ≤ v.1.val := by
  obtain ⟨a, b⟩ := v
  have ha := a.isLt
  have hb := b.isLt
  simp only [hubs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff]
  change (_ ∧ b.val = 0) ∨ (_ ∧ b.val = 1) ∨ (_ ∧ b.val = 0) ∨
    (_ ∧ b.val = 1) ↔ 989 ≤ a.val
  omega

/-- Even if each hub copy uses both cycle edges horizontally, eight edges cannot
reach nine disjoint three-copy windows. -/
private theorem exists_unused_label {X Y : Type*} [Fintype X] [Fintype Y]
    (C : SimpleGraph X) [DecidableRel C.Adj] (hs : Finset X)
    (label : X → Y) (hdeg : ∀ v, C.degree v = 2) (hcard : hs.card * 2 < Fintype.card Y) :
    ∃ k : Y, ∀ u v, u ∈ hs → label v = k → ¬C.Adj u v := by
  classical
  let used := hs.biUnion fun u ↦ (C.neighborFinset u).image label
  have hused : used.card ≤ hs.card * 2 := calc
    _ ≤ ∑ u ∈ hs, ((C.neighborFinset u).image label).card := Finset.card_biUnion_le
    _ ≤ ∑ u ∈ hs, 2 := Finset.sum_le_sum fun u _ ↦
      Finset.card_image_le.trans (hdeg u).le
    _ = _ := by simp
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (t := Finset.univ) (s := used) (by simpa using hused.trans_lt hcard)
  refine ⟨k, ?_⟩
  intro u v hu hv huv
  apply hk
  change k ∈ hs.biUnion (fun u ↦ (C.neighborFinset u).image label)
  rw [← hv, Finset.mem_biUnion]
  have hm : v ∈ C.neighborFinset u := by simpa only [SimpleGraph.mem_neighborFinset] using huv
  exact ⟨u, hu, Finset.mem_image_of_mem label hm⟩

theorem exists_clean_window (C : SimpleGraph P) [DecidableRel C.Adj]
    (hdeg : ∀ v, C.degree v = 2) :
    ∃ k : Fin 9, ∀ u v, 989 ≤ u.1.val → v.1.val / 114 = k.val → ¬C.Adj u v := by
  obtain ⟨k, hk⟩ := exists_unused_label C hubs window hdeg (by decide +kernel)
  exact ⟨k, fun u v hu hv ↦ hk u v (mem_hubs.mpr hu) (Fin.ext hv)⟩

/-- A nontrivial finite cut of a connected graph has a crossing edge. -/
private theorem exists_edge_across {X : Type*} {C : SimpleGraph X} (hc : C.Connected)
    {s : Set X} {u v : X} (hu : u ∈ s) (hv : v ∉ s) :
    ∃ a ∈ s, ∃ b ∉ s, C.Adj a b := by
  obtain ⟨p⟩ := hc.preconnected u v
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
    by_cases hw : w ∈ s
    · exact ih hw hv
    · exact ⟨u, hu, w, hw, huw⟩

end Prism8339

open SimpleGraph PrismLocal
open scoped BigOperators

namespace Prism8339

/-- Four distinct edges at the two degree-two copies of a base vertex use all available slots. -/
private theorem saturate_terminal {X : Type*} [Fintype X]
    (C : SimpleGraph (X × Fin 2)) [DecidableRel C.Adj] (hdeg : ∀ v, C.degree v = 2)
    (b : X) (w : Fin 4 → Fin 2 × (X × Fin 2)) (hinj : Function.Injective w)
    (hsel : ∀ f, C.Adj (b, (w f).1) (w f).2) :
    ∀ l q, C.Adj (b, l) q → ∃ f, w f = (l, q) := by
  classical
  let ns := (Finset.univ : Finset (Fin 2)).biUnion fun l ↦
    (C.neighborFinset (b, l)).image (l, ·)
  have hm (l : Fin 2) (q : X × Fin 2) (h : C.Adj (b, l) q) : (l, q) ∈ ns := by
    have ha : q ∈ C.neighborFinset (b, l) := by simpa only [mem_neighborFinset] using h
    exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Finset.mem_image_of_mem (l, ·) ha⟩
  have hcard : ns.card ≤ 4 := calc
    _ ≤ ∑ l : Fin 2, ((C.neighborFinset (b, l)).image (l, ·)).card := Finset.card_biUnion_le
    _ ≤ ∑ l : Fin 2, 2 := Finset.sum_le_sum fun l _ ↦
      Finset.card_image_le.trans (hdeg (b, l)).le
    _ = 4 := by simp
  let chosen := (Finset.univ : Finset (Fin 4)).image w
  have hsub : chosen ⊆ ns := by
    intro v hv
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hv
    simpa only [Prod.mk.eta] using hm (w f).1 (w f).2 (hsel f)
  have hchosen : chosen.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have heq := Finset.eq_of_subset_of_card_le hsub (hchosen ▸ hcard)
  intro l q hq
  have hh := hm l q hq
  rw [← heq] at hh
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hh
  exact ⟨f, hf⟩

/-- A Hamiltonian graph cannot have one edge across a nontrivial vertex cut. -/
private theorem no_single_exit {X : Type*} [Fintype X] [DecidableEq X] {C : SimpleGraph X}
    (hC : C.IsHamiltonian) (s : Set X) {u v : X} (hu : u ∈ s) (hv : v ∉ s)
    (unique : ∀ a ∈ s, ∀ b ∉ s, C.Adj a b → a = u ∧ b = v) : False := by
  classical
  apply (isBridge_iff (G := C) (u := u) (v := v)).mpr ?_ |>.not_isHamiltonian hC
  rintro ⟨p⟩
  have hw (a b : X) (p' : (C.deleteEdges {s(u, v)}).Walk a b) (ha : a ∈ s) : b ∈ s := by
    induction p' with
    | nil => exact ha
    | @cons a c b hac p' ih =>
      apply ih
      by_contra hc
      obtain ⟨hau, hcv⟩ := unique a ha c hc (deleteEdges_adj.mp hac).1
      exact (deleteEdges_adj.mp hac).2 (by simp [hau, hcv])
  exact hv (hw _ _ p hu)

abbrev A := Fin 9 × Fin 2

private abbrev CleanArms (C : SimpleGraph P) (i : Fin 26) :=
  ∀ u v : P, 989 ≤ u.1.val → 38 * i.val < v.1.val → v.1.val < 38 * i.val + 34 → ¬C.Adj u v

private theorem arm_chain_adj (C : SimpleGraph P) (hle : C ≤ prism)
    (i : Fin 26) (cl : CleanArms C i) (f : Fin 4) (p : A) (q : P)
    (hp : p.1 ≠ 0) (ha : C.Adj (armEmbedding i f p) q) :
    q = (atCopy i 17, p.2) ∨
      ∃ r, r ∈ localNbr PrismLocal.armEdges p ∧ armEmbedding i f r = q := by
  obtain ⟨hlo, hhi⟩ := armEmbedding_is_inside i f hp
  exact arm_neighbors i f p q hp (by by_contra h; exact cl q _ (by omega) hlo hhi ha.symm)
    (hle ha)

private theorem arm_has_contact (C : SimpleGraph P) [DecidableRel C.Adj] (hle : C ≤ prism)
    (hc : C.Connected) (hdeg : ∀ v, C.degree v = 2) (i : Fin 26) (cl : CleanArms C i) (f : Fin 4) :
    ∃ p : A, p.1 ≠ 0 ∧ C.Adj (armEmbedding i f p) (atCopy i 17, p.2) := by
  by_contra! h
  let e := armEmbedding i f
  have hn : ∀ p : A, p.1 ≠ 0 → incidentWeight (cycleWeight C e) PrismLocal.armEdges p = 2 := by
    intro p hp
    apply incidentWeight_eq_two C e _ p (armNbr_nodup p) (hdeg (e p))
    intro q hq
    rcases arm_chain_adj C hle i cl f p q hp hq with hport | H
    · exact (h p hp (hport ▸ hq)).elim
    · exact H
  have hout : ∃ p : P, p ∉ Set.range e := by
    refine ⟨(989, 0), ?_⟩
    rintro ⟨p, h⟩
    have hv := congrArg (fun p : P ↦ p.1.val) h
    have hi := i.isLt
    have hf := (armLabel f p.1).isLt
    change 38 * i.val + (armLabel f p.1).val = 989 at hv
    omega
  apply arm_impossible (cycleWeight C e) _ hn
    (noTrap_cycleWeight C e _ armNbr_nodup hdeg hc hout)
  intro ab
  unfold cycleWeight
  split <;> omega

private theorem arm_near_contact_of_unique (C : SimpleGraph P) (hle : C ≤ prism)
    (hham : C.IsHamiltonian) (i : Fin 26) (cl : CleanArms C i) (f : Fin 4)
    (x : A) (hx : x.1 ≠ 0)
    (hun : ∀ p : A, p.1 ≠ 0 → C.Adj (armEmbedding i f p) (atCopy i 17, p.2) → p = x) :
    ∃ y : A, y.1 ≠ 0 ∧ ∃ l : Fin 2, C.Adj (armEmbedding i f y) (armEmbedding i f (0, l)) := by
  by_contra! h
  let e := armEmbedding i f
  let cut : Set P := {v | ∃ q : A, q.1 ≠ 0 ∧ e q = v}
  have hxcut : e x ∈ cut := ⟨x, hx, rfl⟩
  have hbar : (atCopy i 17, x.2) ∉ cut := by
    rintro ⟨z, hz, hz'⟩
    have hval := congrArg (fun p : P ↦ p.1.val) hz'
    have hzz : 0 < z.1.val := Nat.pos_of_ne_zero fun he ↦ hz (Fin.ext he)
    have hf := (armLabel_cast f z.1 hzz).2.2
    change 38 * i.val + (armLabel f z.1).val = 38 * i.val + 17 at hval
    omega
  apply no_single_exit hham cut hxcut hbar
  rintro a ⟨w, hw, rfl⟩ b hb hab
  rcases arm_chain_adj C hle i cl f w b hw hab with hh | ⟨r, _, hr⟩
  · have he : w = x := hun w hw (hh ▸ hab)
    subst w
    exact ⟨rfl, hh⟩
  · by_cases hr0 : r.1 = 0
    · have hrr : r = (0, r.2) := Prod.ext hr0 rfl
      exact (h w hw r.2 (by simpa only [← hr, ← hrr] using hab)).elim
    · exact (hb ⟨r, hr0, hr⟩).elim

/-- The clean copy has a selected arm edge from each arm to its outer terminal. -/
theorem clean_copy_contacts (C : SimpleGraph P) [DecidableRel C.Adj] (hle : C ≤ prism)
    (hham : C.IsHamiltonian) (hc : C.Connected) (hdeg : ∀ v, C.degree v = 2)
    (i : Fin 26) (cl : CleanArms C i) :
    ∀ f : Fin 4, ∃ y : A, y.1 ≠ 0 ∧ ∃ l : Fin 2,
      C.Adj (armEmbedding i f y) (armEmbedding i f (0, l)) := by
  choose x hx hsel using arm_has_contact C hle hc hdeg i cl
  let w (f : Fin 4) := ((x f).2, armEmbedding i f (x f))
  have distinct (f g : Fin 4) {a b : A} (ha : a.1 ≠ 0) (hb : b.1 ≠ 0)
      (h : armEmbedding i f a = armEmbedding i g b) : f = g := by
    have hv := congrArg (fun p : P ↦ p.1.val) h
    simp only [armEmbedding_val] at hv
    apply armLabel_disjoint f g a.1 b.1
    · exact fun he ↦ ha (Fin.ext he)
    · exact fun he ↦ hb (Fin.ext he)
    · exact Fin.ext (by omega)
  have hinj : Function.Injective w := by
    intro f g h
    exact distinct f g (hx f) (hx g) (congrArg Prod.snd h)
  have hsat := saturate_terminal C hdeg (atCopy i 17) w hinj (fun f ↦ (hsel f).symm)
  intro f
  apply arm_near_contact_of_unique C hle hham i cl f (x f) (hx f)
  intro y hy h
  obtain ⟨g, hg⟩ := hsat y.2 _ h.symm
  have hh := congrArg Prod.snd hg
  change armEmbedding i g (x g) = armEmbedding i f y at hh
  have hg' := distinct g f (hx g) hy hh
  subst g
  exact (armEmbedding i f).injective hh.symm

end Prism8339

namespace Prism8339

open SimpleGraph
open PrismLocal

private abbrev RVertex := Fin 5 × Fin 2
local notation "loR[" i "]" => (38 * Fin.val (i : Fin 26) + 34)
local notation "hiR[" i "]" => (38 * Fin.val (i : Fin 26) + 38)
private abbrev InRight (i : Fin 26) (v : P) := loR[i] ≤ v.1.val ∧ v.1.val ≤ hiR[i]

private theorem rightEmbedding_inRight (i : Fin 26) (x : RVertex) :
    InRight i (rightEmbedding i x) := by
  simp only [InRight, rightEmbedding_val]
  omega

private def rightLocal (i : Fin 26) (v : P) (hv : InRight i v) : RVertex :=
  (⟨v.1.val - loR[i], by have := hv.2; omega⟩, v.2)

private theorem rightEmbedding_rightLocal (i : Fin 26) (v : P) (hv : InRight i v) :
    rightEmbedding i (rightLocal i v hv) = v := by
  apply Prod.ext
  · apply Fin.ext
    have := hv.1
    simp only [rightEmbedding_val, rightLocal]
    omega
  · rfl

private theorem rightLocal_rightEmbedding (i : Fin 26) (x : RVertex)
    (hx : InRight i (rightEmbedding i x)) : rightLocal i (rightEmbedding i x) hx = x :=
  (rightEmbedding i).injective (rightEmbedding_rightLocal i _ hx)

private theorem terminal_eq_embedding (i : Fin 26) (a : Fin 5) {v : P}
    (hv : v.1.val = loR[i] + a.val) : rightEmbedding i (a, v.2) = v := by
  apply Prod.ext
  · apply Fin.ext
    simp only [rightEmbedding_val]
    omega
  · rfl

private def rightBaseEdges : List (ℕ × ℕ) :=
  [(34, 35), (35, 38), (34, 36), (36, 37), (37, 38)]

private theorem left_hright {e : ℕ × ℕ} (he : e ∈ hEdges) :
    e.2 ≤ 34 ∨ (34 ≤ e.1 ∧ e ∈ rightBaseEdges) := by
  have h : hEdges.all (fun p ↦ decide (p.2 ≤ 34 ∨ (34 ≤ p.1 ∧ p ∈ rightBaseEdges))) = true :=
    by decide
  exact of_decide_eq_true (List.all_eq_true.mp h _ he)

private theorem right_horizontal (a b : Fin 5) (t : Fin 2)
    (he : (34 + a.val, 34 + b.val) ∈ rightBaseEdges) : ((a, t), (b, t)) ∈ rightEdges := by
  fin_cases a <;> fin_cases b <;> fin_cases t <;> revert he <;> decide

private theorem right_vertical (a : Fin 5) (s t : Fin 2)
    (ha0 : a ≠ 0) (ha4 : a ≠ 4) (hst : s ≠ t) :
    ((a, s), (a, t)) ∈ rightEdges ∨ ((a, t), (a, s)) ∈ rightEdges := by
  fin_cases a <;> fin_cases s <;> fin_cases t <;> revert ha0 ha4 hst <;> decide

private def RightListed (i : Fin 26) (u v : P) : Prop :=
  ∃ a b : RVertex, rightEmbedding i a = u ∧ rightEmbedding i b = v ∧
    b ∈ localNbr rightEdges a

private theorem RightListed.symm {i : Fin 26} {u v : P} (h : RightListed i u v) :
    RightListed i v u := by
  obtain ⟨a, b, ha, hb, hn⟩ := h
  exact ⟨b, a, hb, ha, mem_localNbr_iff.mpr (mem_localNbr_iff.mp hn).symm⟩

private abbrev RightOther (i : Fin 26) (u v : P) :=
  v.1.val < loR[i] ∨ hiR[i] < u.1.val ∨
  (u.1.val < loR[i] ∧ v.1.val = loR[i]) ∨
  (u.1.val = hiR[i] ∧ hiR[i] < v.1.val) ∨
  (u.1.val = loR[i] ∧ v.1.val = loR[i]) ∨
  (u.1.val = hiR[i] ∧ v.1.val = hiR[i])

private theorem ordered_horizontal (i : Fin 26) {u v : P} (ho : u.1.val ≤ v.1.val)
    (hv : v.1.val < 989) (h : graph.Adj u.1 v.1) (hl : u.2 = v.2) :
    RightListed i u v ∨ RightOther i u v := by
  obtain ⟨k, e, he, hh | hh⟩ := (chain_adj_iff (by omega : u.1.val < 989) hv).mp h
  · obtain ⟨he12, he2⟩ := hEdges_bounds he
    have huv : u.1.val < v.1.val := by omega
    by_cases hki : k.val < i.val
    · right
      unfold RightOther
      omega
    by_cases hik : i.val < k.val
    · right
      unfold RightOther
      omega
    have hk : k = i := Fin.ext (by omega)
    subst k
    rcases left_hright he with hleft | ⟨h34, hright⟩
    · right
      unfold RightOther
      omega
    · have hu' : InRight i u := ⟨by omega, by omega⟩
      have hv' : InRight i v := ⟨by omega, by omega⟩
      let a := rightLocal i u hu'
      let b := rightLocal i v hv'
      have hbase : (34 + a.1.val, 34 + b.1.val) ∈ rightBaseEdges := by
        change (34 + (u.1.val - loR[i]), 34 + (v.1.val - loR[i])) ∈ rightBaseEdges
        rwa [show 34 + (u.1.val - loR[i]) = e.1 by omega,
          show 34 + (v.1.val - loR[i]) = e.2 by omega, Prod.mk.eta]
      have hl' : a.2 = b.2 := hl
      left
      refine ⟨a, b, rightEmbedding_rightLocal i u hu', rightEmbedding_rightLocal i v hv', ?_⟩
      apply mem_localNbr_iff.mpr
      left
      have heq : ((a.1, a.2), (b.1, a.2)) = (a, b) :=
        Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl hl')
      exact heq ▸ right_horizontal a.1 b.1 a.2 hbase
  · have := (hEdges_bounds he).1
    omega

private theorem ordered_vertical (i : Fin 26) {u v : P} (hbase : u.1 = v.1)
    (hl : u.2 ≠ v.2) : RightListed i u v ∨ RightOther i u v := by
  have hval := congrArg Fin.val hbase
  by_cases h : u.1.val ≤ loR[i] ∨ hiR[i] ≤ u.1.val
  · right
    unfold RightOther
    omega
  left
  have hu : InRight i u := ⟨by omega, by omega⟩
  have hv : InRight i v := ⟨by omega, by omega⟩
  let a := rightLocal i u hu
  let b := rightLocal i v hv
  have hsame : a.1 = b.1 := Fin.ext (by change u.1.val - loR[i] = v.1.val - loR[i]; omega)
  have ha0 : a.1 ≠ 0 := by
    intro h0
    have h' := congrArg Fin.val h0
    change u.1.val - loR[i] = 0 at h'
    omega
  have ha4 : a.1 ≠ 4 := by
    intro h4
    have h' := congrArg Fin.val h4
    change u.1.val - loR[i] = 4 at h'
    omega
  refine ⟨a, b, rightEmbedding_rightLocal i u hu, rightEmbedding_rightLocal i v hv, ?_⟩
  have hb' : (a.1, v.2) = b := Prod.ext hsame rfl
  have hmem := right_vertical a.1 u.2 v.2 ha0 ha4 hl
  exact mem_localNbr_iff.mpr (hb' ▸ hmem)

private theorem ordered_right_adj (i : Fin 26) {u v : P} (ho : u.1.val ≤ v.1.val)
    (hv : v.1.val < 989) (h : prism.Adj u v) : RightListed i u v ∨ RightOther i u v := by
  rcases boxProd_adj.mp h with ⟨hh, ht⟩ | ⟨ht, hh⟩
  · exact ordered_horizontal i ho hv hh ht
  · exact ordered_vertical i hh ht

private theorem listed_of_interior (i : Fin 26) {u v : P} (hu : u.1.val < 989)
    (hv : v.1.val < 989) (hlo : loR[i] < u.1.val) (hhi : u.1.val < hiR[i])
    (h : prism.Adj u v) : RightListed i u v := by
  rcases le_total u.1.val v.1.val with hle | hle
  · rcases ordered_right_adj i hle hv h with hr | ho
    · exact hr
    · unfold RightOther at ho
      omega
  · rcases ordered_right_adj i hle hu h.symm with hr | ho
    · exact hr.symm
    · unfold RightOther at ho
      omega

private theorem rightNbr_nodup (x : RVertex) : (localNbr rightEdges x).Nodup := by
  obtain ⟨a, t⟩ := x
  fin_cases a <;> fin_cases t <;> decide

private theorem terminal_nbr_other_base (a : Fin 5) (t : Fin 2) (x : RVertex)
    (ha : a = 0 ∨ a = 4) (hx : x ∈ localNbr rightEdges (a, t)) : x.1 ≠ a := by
  obtain ⟨b, s⟩ := x
  fin_cases a <;> fin_cases t <;> fin_cases b <;> fin_cases s <;> revert ha hx <;> decide

private abbrev rWeight (C : SimpleGraph P) [DecidableRel C.Adj] (i : Fin 26) :=
  cycleWeight C (rightEmbedding i)

private abbrev rDegree (C : SimpleGraph P) [DecidableRel C.Adj] (i : Fin 26) (x : RVertex) :=
  incidentWeight (rWeight C i) rightEdges x

private abbrev rSelected (C : SimpleGraph P) [DecidableRel C.Adj] (i : Fin 26) (x : RVertex) :=
  selectedNbr C (rightEmbedding i) rightEdges x

private theorem selected_inRight (C : SimpleGraph P) [DecidableRel C.Adj] (i : Fin 26)
    {x : RVertex} {v : P} (hv : v ∈ rSelected C i x) : InRight i v := by
  obtain ⟨_, y, _, rfl⟩ := (mem_selectedNbr_iff C (rightEmbedding i)).mp hv
  exact rightEmbedding_inRight i y

private theorem terminal_notMem_selected (C : SimpleGraph P) [DecidableRel C.Adj] (i : Fin 26)
    {a : Fin 5} {t : Fin 2} (ha : a = 0 ∨ a = 4) {v : P}
    (hv : v.1.val = loR[i] + a.val) : v ∉ rSelected C i (a, t) := by
  intro h
  obtain ⟨_, x, hx, hEq⟩ := (mem_selectedNbr_iff C (rightEmbedding i)).mp h
  have hval : (rightEmbedding i x).1.val = v.1.val := congrArg (fun z : P ↦ z.1.val) hEq
  simp only [rightEmbedding_val] at hval
  exact terminal_nbr_other_base a t x ha hx (Fin.ext (by omega))

private theorem right_interior_degree (C : SimpleGraph P) [DecidableRel C.Adj] (i : Fin 26)
    (hle : C ≤ prism) (hdeg : ∀ v, C.degree v = 2)
    (hhub : ∀ u v : P, loR[i] ≤ u.1.val → u.1.val ≤ hiR[i] → 989 ≤ v.1.val → ¬ C.Adj u v)
    (x : RVertex) (hx0 : x.1 ≠ 0) (hx4 : x.1 ≠ 4) : rDegree C i x = 2 := by
  apply incidentWeight_eq_two C (rightEmbedding i) rightEdges x (rightNbr_nodup x) (hdeg _)
  intro v hv
  have hx := rightEmbedding_inRight i x
  have hv' : v.1.val < 989 := by
    by_contra! h
    exact hhub _ _ hx.1 hx.2 h hv
  have hlo : loR[i] < (rightEmbedding i x).1.val := by
    have h0 : x.1.val ≠ 0 := fun h ↦ hx0 (Fin.ext h)
    rw [rightEmbedding_val]
    omega
  have hhi : (rightEmbedding i x).1.val < hiR[i] := by
    have h4 : x.1.val ≠ 4 := fun h ↦ hx4 (Fin.ext h)
    rw [rightEmbedding_val]
    omega
  have hx' : (rightEmbedding i x).1.val < 989 := by rw [rightEmbedding_val]; omega
  obtain ⟨a, b, ha, hb, hn⟩ := listed_of_interior i hx' hv' hlo hhi (hle hv)
  have hEq := (rightEmbedding i).injective ha
  exact ⟨b, hEq ▸ hn, hb⟩

private theorem insert_subset_of_mem {X : Type*} [DecidableEq X] {s t : Finset X} {v : X}
    (h : s ⊆ t) (hv : v ∈ t) : insert v s ⊆ t := by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact hv
  · exact h hw

private theorem local_degree_lt_of_unselected {L X : Type*} [DecidableEq L]
    [Fintype X] (C : SimpleGraph X) [DecidableRel C.Adj]
    (e : L ↪ X) (edges : List (L × L)) (x : L) (hdeg : C.degree (e x) = 2)
    (hnodup : (localNbr edges x).Nodup) {v : X} (hv : C.Adj (e x) v)
    (hnot : v ∉ selectedNbr C e edges x) : incidentWeight (cycleWeight C e) edges x < 2 := by
  classical
  have hsub := selectedNbr_subset_neighborFinset C e edges x
  have hvMem : v ∈ C.neighborFinset (e x) := (C.mem_neighborFinset _ _).mpr hv
  have hcard := Finset.card_le_card (insert_subset_of_mem hsub hvMem)
  rw [Finset.card_insert_of_notMem hnot, C.card_neighborFinset_eq_degree, hdeg,
    ← incidentWeight_eq_card_selectedNbr C e edges x hnodup] at hcard
  omega

private theorem local_degree_zero_of_two_unselected {L X : Type*} [DecidableEq L]
    [Fintype X] (C : SimpleGraph X) [DecidableRel C.Adj]
    (e : L ↪ X) (edges : List (L × L)) (x : L) (hdeg : C.degree (e x) = 2)
    (hnodup : (localNbr edges x).Nodup) {v w : X} (hv : C.Adj (e x) v) (hw : C.Adj (e x) w)
    (hv' : v ∉ selectedNbr C e edges x) (hw' : w ∉ selectedNbr C e edges x) (hne : v ≠ w) :
    incidentWeight (cycleWeight C e) edges x = 0 := by
  classical
  have hsub := selectedNbr_subset_neighborFinset C e edges x
  have hvMem : v ∈ C.neighborFinset (e x) := (C.mem_neighborFinset _ _).mpr hv
  have hwMem : w ∈ C.neighborFinset (e x) := (C.mem_neighborFinset _ _).mpr hw
  have hsub' := insert_subset_of_mem hsub hwMem
  have hcard := Finset.card_le_card (insert_subset_of_mem hsub' hvMem)
  have hnot : v ∉ insert w (selectedNbr C e edges x) := by simp [hne, hv']
  rw [Finset.card_insert_of_notMem hnot, Finset.card_insert_of_notMem hw',
    C.card_neighborFinset_eq_degree, hdeg,
    ← incidentWeight_eq_card_selectedNbr C e edges x hnodup] at hcard
  omega

private theorem right_degree_lt_of_unselected (C : SimpleGraph P) [DecidableRel C.Adj]
    (i : Fin 26) (hdeg : ∀ v, C.degree v = 2) {x : RVertex} {v : P}
    (hv : C.Adj (rightEmbedding i x) v) (hnot : v ∉ rSelected C i x) : rDegree C i x < 2 :=
  local_degree_lt_of_unselected C (rightEmbedding i) rightEdges x (hdeg _) (rightNbr_nodup x)
    hv hnot

private theorem right_degree_zero_of_two_unselected (C : SimpleGraph P) [DecidableRel C.Adj]
    (i : Fin 26) (hdeg : ∀ v, C.degree v = 2) {x : RVertex} {v w : P}
    (hv : C.Adj (rightEmbedding i x) v) (hw : C.Adj (rightEmbedding i x) w)
    (hv' : v ∉ rSelected C i x) (hw' : w ∉ rSelected C i x) (hne : v ≠ w) :
    rDegree C i x = 0 :=
  local_degree_zero_of_two_unselected C (rightEmbedding i) rightEdges x (hdeg _)
    (rightNbr_nodup x) hv hw hv' hw' hne

/-- Two distinct selected edges directed from the given terminal to its exterior side. -/
def HasTwoTerminalExits (C : SimpleGraph P) (label : ℕ) (outside : P → Prop) : Prop :=
  ∃ p₁ q₁ p₂ q₂ : P, p₁.1.val = label ∧ p₂.1.val = label ∧
    outside q₁ ∧ outside q₂ ∧ C.Adj p₁ q₁ ∧ C.Adj p₂ q₂ ∧ (p₁, q₁) ≠ (p₂, q₂)

private theorem layer_cases (t : Fin 2) : t = 0 ∨ t = 1 := by
  fin_cases t <;> decide

private theorem right_terminal_degree_bound (C : SimpleGraph P) [DecidableRel C.Adj]
    (i : Fin 26) (a : Fin 5) (hdeg : ∀ v, C.degree v = 2) {outside : P → Prop}
    (hout : ∀ v, outside v → ¬ InRight i v)
    (hexits : HasTwoTerminalExits C (loR[i] + a.val) outside) :
    rDegree C i (a, 0) + rDegree C i (a, 1) ≤ 2 := by
  obtain ⟨p, v, q, w, hp, hq, hv, hw, hpv, hqw, hpair⟩ := hexits
  have hp' := terminal_eq_embedding i a hp
  have hq' := terminal_eq_embedding i a hq
  have hv' : v ∉ rSelected C i (a, p.2) := fun h ↦ hout v hv (selected_inRight C i h)
  have hw' : w ∉ rSelected C i (a, q.2) := fun h ↦ hout w hw (selected_inRight C i h)
  have hpv' : C.Adj (rightEmbedding i (a, p.2)) v := hp' ▸ hpv
  have hqw' : C.Adj (rightEmbedding i (a, q.2)) w := hq' ▸ hqw
  by_cases ht : p.2 = q.2
  · have hpq : p = q := by
      calc
        p = rightEmbedding i (a, p.2) := hp'.symm
        _ = rightEmbedding i (a, q.2) := by rw [ht]
        _ = q := hq'
    have hne : v ≠ w := fun h ↦ hpair (Prod.ext hpq h)
    rw [← ht] at hw' hqw'
    have hz := right_degree_zero_of_two_unselected C i hdeg hpv' hqw' hv' hw' hne
    have hb (t : Fin 2) :=
      incidentWeight_le_two C (rightEmbedding i) rightEdges (a, t) (rightNbr_nodup _) (hdeg _)
    rcases layer_cases p.2 with h | h
    · rw [h] at hz
      rw [hz, zero_add]
      exact hb 1
    · rw [h] at hz
      rw [hz, add_zero]
      exact hb 0
  · have hb₁ := right_degree_lt_of_unselected C i hdeg hpv' hv'
    have hb₂ := right_degree_lt_of_unselected C i hdeg hqw' hw'
    rcases layer_cases p.2 with hp₂ | hp₂ <;> rcases layer_cases q.2 with hq₂ | hq₂
    · exact (ht (hp₂.trans hq₂.symm)).elim
    · rw [hp₂] at hb₁
      rw [hq₂] at hb₂
      omega
    · rw [hp₂] at hb₁
      rw [hq₂] at hb₂
      omega
    · exact (ht (hp₂.trans hq₂.symm)).elim

/-- The local coloring certificate for `R`, stated as an input to the gluing argument. -/
def RightColoringCertificate : Prop :=
  ∀ w : RVertex × RVertex → ℕ,
    (∀ v : RVertex, v.1 ≠ 0 → v.1 ≠ 4 → incidentWeight w rightEdges v = 2) →
    (incidentWeight w rightEdges (0, 0) + incidentWeight w rightEdges (0, 1) ≤ 2) →
    (incidentWeight w rightEdges (4, 0) + incidentWeight w rightEdges (4, 1) ≤ 2) →
    NoTrap w rightEdges →
    ∃ f : RVertex → Bool,
      (∀ e ∈ rightEdges, 0 < w e → f e.1 = f e.2) ∧
      (∀ t, incidentWeight w rightEdges (0, t) < 2 → f (0, t) = false) ∧
      (∀ t, incidentWeight w rightEdges (4, t) < 2 → f (4, t) = true)

/-- A coloring separates the two sides of `Rᵢ` using only the selected hub-free edges. -/
def RightBarrier (C : SimpleGraph P) (i : Fin 26) : Prop :=
  ∃ f : P → Bool,
    (∀ v, v.1.val < loR[i] → f v = false) ∧
    (∀ v, hiR[i] < v.1.val → f v = true) ∧
    (∀ u v, u.1.val < 989 → v.1.val < 989 → C.Adj u v → f u = f v)

private def glueRightColor (i : Fin 26) (f : RVertex → Bool) (v : P) : Bool :=
  if h : InRight i v then f (rightLocal i v h) else decide (hiR[i] < v.1.val)

private theorem glueRightColor_left (i : Fin 26) (f : RVertex → Bool) {v : P}
    (hv : v.1.val < loR[i]) : glueRightColor i f v = false := by
  have hout : ¬ InRight i v := fun h ↦ (Nat.not_le_of_lt hv) h.1
  simp [glueRightColor, hout, show ¬ hiR[i] < v.1.val by omega]

private theorem glueRightColor_right (i : Fin 26) (f : RVertex → Bool) {v : P}
    (hv : hiR[i] < v.1.val) : glueRightColor i f v = true := by
  have hout : ¬ InRight i v := fun h ↦ (Nat.not_le_of_lt hv) h.2
  simp [glueRightColor, hout, hv]

private theorem glueRightColor_embedding (i : Fin 26) (f : RVertex → Bool) (x : RVertex) :
    glueRightColor i f (rightEmbedding i x) = f x := by
  rw [glueRightColor, dite_eq_left (rightEmbedding_inRight i x), rightLocal_rightEmbedding]

private theorem glueRightColor_terminal (C : SimpleGraph P) [DecidableRel C.Adj] (i : Fin 26)
    (hdeg : ∀ v, C.degree v = 2) (f : RVertex → Bool) {a : Fin 5} {c : Bool}
    (hf : ∀ t, rDegree C i (a, t) < 2 → f (a, t) = c) {u v : P}
    (hu : u.1.val = loR[i] + a.val) (h : C.Adj u v)
    (hunlisted : v ∉ rSelected C i (a, u.2)) : glueRightColor i f u = c := by
  have he := terminal_eq_embedding i a hu
  calc
    _ = f (a, u.2) := he ▸ glueRightColor_embedding i f (a, u.2)
    _ = c := hf u.2 (right_degree_lt_of_unselected C i hdeg (he ▸ h) hunlisted)

/-- The local `R` certificate lifts to a barrier when both terminal pairs have two exits. -/
theorem right_barrier (right_coloring : RightColoringCertificate)
    (C : SimpleGraph P) [DecidableRel C.Adj] (i : Fin 26)
    (hle : C ≤ prism) (hdeg : ∀ p, C.degree p = 2) (hc : C.Connected)
    (hhub : ∀ u v : P, loR[i] ≤ u.1.val → u.1.val ≤ hiR[i] → 989 ≤ v.1.val → ¬ C.Adj u v)
    (hl : HasTwoTerminalExits C loR[i] (fun v ↦ v.1.val < loR[i]))
    (hr : HasTwoTerminalExits C hiR[i] (fun v ↦ hiR[i] < v.1.val)) : RightBarrier C i := by
  have hL : rDegree C i (0, 0) + rDegree C i (0, 1) ≤ 2 :=
    right_terminal_degree_bound C i 0 hdeg (fun v hv h ↦ (Nat.not_le_of_lt hv) h.1) hl
  have hR : rDegree C i (4, 0) + rDegree C i (4, 1) ≤ 2 :=
    right_terminal_degree_bound C i 4 hdeg (fun v hv h ↦ (Nat.not_le_of_lt hv) h.2) (by
      simpa only [show loR[i] + (4 : Fin 5).val = hiR[i] by omega] using hr)
  have hout : ∃ p : P, p ∉ Set.range (rightEmbedding i) := by
    refine ⟨(989, 0), ?_⟩
    rintro ⟨x, hx⟩
    have h := (rightEmbedding_inRight i x).2
    rw [hx] at h
    change 989 ≤ hiR[i] at h
    omega
  have hno := noTrap_cycleWeight C (rightEmbedding i) rightEdges rightNbr_nodup hdeg hc hout
  obtain ⟨f, hf, hfL, hfR⟩ :=
    right_coloring (rWeight C i) (right_interior_degree C i hle hdeg hhub) hL hR hno
  refine ⟨glueRightColor i f, fun _ ↦ glueRightColor_left i f,
    fun _ ↦ glueRightColor_right i f, ?_⟩
  have hL' {u v : P} (hu : u.1.val = loR[i]) (h : C.Adj u v)
      (hnot : v ∉ rSelected C i (0, u.2)) : glueRightColor i f u = false :=
    glueRightColor_terminal C i hdeg f hfL hu h hnot
  have hR' {u v : P} (hu : u.1.val = hiR[i]) (h : C.Adj u v)
      (hnot : v ∉ rSelected C i (4, u.2)) : glueRightColor i f u = true :=
    glueRightColor_terminal C i hdeg f hfR (by omega) h hnot
  have ordered (u v : P) (ho : u.1.val ≤ v.1.val) (hv : v.1.val < 989) (h : C.Adj u v) :
      glueRightColor i f u = glueRightColor i f v := by
    rcases ordered_right_adj i ho hv (hle h) with hlist | hother
    · obtain ⟨a, b, rfl, rfl, hm⟩ := hlist
      rw [glueRightColor_embedding, glueRightColor_embedding]
      rcases mem_localNbr_iff.mp hm with he | he
      · exact hf (a, b) he (by simp [cycleWeight, h])
      · exact (hf (b, a) he (by simp [cycleWeight, h.symm])).symm
    · rcases hother with hh | hh | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [glueRightColor_left i f (by omega : u.1.val < loR[i]), glueRightColor_left i f hh]
      · rw [glueRightColor_right i f hh, glueRightColor_right i f (by omega : hiR[i] < v.1.val)]
      · rw [glueRightColor_left i f hu, hL' hv h.symm]
        exact fun hm ↦ (Nat.not_le_of_lt hu) (selected_inRight C i hm).1
      · rw [glueRightColor_right i f hv, hR' hu h]
        exact fun hm ↦ (Nat.not_le_of_lt hv) (selected_inRight C i hm).2
      · rw [hL' hu h, hL' hv h.symm]
        all_goals exact terminal_notMem_selected C i (Or.inl rfl) (by omega)
      · rw [hR' hu h, hR' hv h.symm]
        all_goals exact terminal_notMem_selected C i (Or.inr rfl) (by omega)
  intro u v hu hv h
  rcases le_total u.1.val v.1.val with ho | ho
  · exact ordered u v ho hv h
  · exact (ordered v u ho hu h.symm).symm

end Prism8339

namespace Prism8339

local notation "P" => V × Fin 2

/-- No selected edge joins a hub to a vertex of window `k`. -/
def Clean (C : SimpleGraph P) (k : Fin 9) : Prop :=
  ∀ u v, 989 ≤ u.1.val → v.1.val / 114 = k.val → ¬C.Adj u v

private theorem window_edge_across {X : Type*} {C : SimpleGraph X} (hc : C.Connected)
    {s : Set X} {u v : X} (hu : u ∈ s) (hv : v ∉ s) :
    ∃ a ∈ s, ∃ b ∉ s, C.Adj a b := by
  obtain ⟨p⟩ := hc.preconnected u v
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
    by_cases hw : w ∈ s
    · exact ih hw hv
    · exact ⟨u, hu, w, hw, huw⟩

/-- A nonempty subset of the nonhub vertices of a clean window must have a nonhub exit. -/
private theorem clean_cut_absurd (C : SimpleGraph P) (k : Fin 9)
    (hc : C.Connected) (hclean : Clean C k) {s : Set P} {w : P} (hw : w ∈ s)
    (hwindow : ∀ u ∈ s, u.1.val < 989 ∧ u.1.val / 114 = k.val)
    (hclosed : ∀ u v, u ∈ s → v.1.val < 989 → C.Adj u v → v ∈ s) : False := by
  let hub : P := (989, 0)
  have hhub : hub ∉ s := fun hm ↦ (by decide : ¬ hub.1.val < 989) (hwindow hub hm).1
  obtain ⟨u, hu, v, hv, hadj⟩ := window_edge_across hc hw hhub
  by_cases hchain : v.1.val < 989
  · exact hv (hclosed u v hu hchain hadj)
  · exact hclean v u (by omega) (hwindow u hu).2 hadj.symm

private theorem barrier_lo {i : Fin 26} {f : P → Bool} {v : P}
    (hleft : ∀ u, u.1.val < 38 * i.val + 34 → f u = false) (hv : f v = true) :
    38 * i.val + 34 ≤ v.1.val := by
  by_contra h
  have h' := hleft v (by omega)
  simp [hv] at h'

private theorem barrier_hi {i : Fin 26} {f : P → Bool} {v : P}
    (hright : ∀ u, 38 * i.val + 38 < u.1.val → f u = true) (hv : f v = false) :
    v.1.val ≤ 38 * i.val + 38 := by
  by_contra h
  have h' := hright v (by omega)
  simp [hv] at h'

/-- A connected spanning cycle cannot have the requisite barriers in a clean window. -/
theorem clean_window_impossible (C : SimpleGraph P) (k : Fin 9) (hc : C.Connected)
    (hclean : Clean C k)
    (hbarrier : ∀ i : Fin 26, i.val = 3 * k.val ∨ (i.val = 3 * k.val + 1 ∧ k.val < 8) →
      RightBarrier C i) : False := by
  have hk := k.isLt
  let i : Fin 26 := ⟨3 * k.val, by omega⟩
  have hi : i.val = 3 * k.val := rfl
  obtain ⟨f, hfl, hfr, hfe⟩ := hbarrier i (Or.inl hi)
  let w : P := (⟨38 * i.val + 39, by omega⟩, 0)
  have hw : w.1.val = 38 * i.val + 39 := rfl
  have hwg : w.1.val < 989 := by omega
  have hwf : f w = true := hfr w (by omega)
  by_cases hlast : k.val < 8
  · let j : Fin 26 := ⟨3 * k.val + 1, by omega⟩
    have hj : j.val = 3 * k.val + 1 := rfl
    obtain ⟨g, hgl, hgr, hge⟩ := hbarrier j (Or.inr ⟨hj, hlast⟩)
    let s : Set P := {v | v.1.val < 989 ∧ f v = true ∧ g v = false}
    have hw' : w ∈ s := ⟨hwg, hwf, hgl w (by omega)⟩
    refine clean_cut_absurd C k hc hclean hw' ?_ ?_
    · intro u hu
      change u.1.val < 989 ∧ f u = true ∧ g u = false at hu
      have hlo := barrier_lo hfl hu.2.1
      have hhi := barrier_hi hgr hu.2.2
      exact ⟨hu.1, by omega⟩
    · intro u v hu hv huv
      change u.1.val < 989 ∧ f u = true ∧ g u = false at hu
      exact ⟨hv, (hfe u v hu.1 hv huv).symm.trans hu.2.1,
        (hge u v hu.1 hv huv).symm.trans hu.2.2⟩
  · have hk' : k.val = 8 := by omega
    let s : Set P := {v | v.1.val < 989 ∧ f v = true}
    have hw' : w ∈ s := ⟨hwg, hwf⟩
    refine clean_cut_absurd C k hc hclean hw' ?_ ?_
    · intro u hu
      change u.1.val < 989 ∧ f u = true at hu
      have hlo := barrier_lo hfl hu.2
      exact ⟨hu.1, by omega⟩
    · intro u v hu hv huv
      change u.1.val < 989 ∧ f u = true at hu
      exact ⟨hv, (hfe u v hu.1 hv huv).symm.trans hu.2⟩

end Prism8339

open SimpleGraph

namespace Prism8339

private theorem outer_contacts (C : SimpleGraph P) [DecidableRel C.Adj] (hle : C ≤ prism)
    (hham : C.IsHamiltonian) (hc : C.Connected) (hdeg : ∀ v, C.degree v = 2)
    (i : Fin 26) (hi : ∀ u v : P, 989 ≤ u.1.val → 38 * i.val < v.1.val →
      v.1.val < 38 * i.val + 34 → ¬C.Adj u v) :
    HasTwoTerminalExits C (38 * i.val) (fun q ↦ 38 * i.val < q.1.val) ∧
      HasTwoTerminalExits C (38 * i.val + 34) (fun q ↦ q.1.val < 38 * i.val + 34) := by
  have h := clean_copy_contacts C hle hham hc hdeg i hi
  have hh (f g : Fin 4) (hne : f ≠ g) (hside : (f.val < 2) ↔ (g.val < 2)) :
      HasTwoTerminalExits C (38 * i.val + (armLabel f 0).val)
        (fun q ↦ 38 * i.val < q.1.val ∧ q.1.val < 38 * i.val + 34) := by
    obtain ⟨a, ha, l, hla⟩ := h f
    obtain ⟨b, hb, m, hmb⟩ := h g
    refine ⟨armEmbedding i f (0, l), armEmbedding i f a, armEmbedding i g (0, m),
      armEmbedding i g b, rfl, ?_, armEmbedding_is_inside i f ha,
      armEmbedding_is_inside i g hb, hla.symm, hmb.symm, ?_⟩
    · simp only [armEmbedding_val, arm_port]
      simp only [hside]
    · intro hab
      have hval := congrArg (fun pp : P × P ↦ pp.2.1.val) hab
      simp only [armEmbedding_val] at hval
      apply hne
      exact armLabel_disjoint f g a.1 b.1 (fun h ↦ ha (Fin.ext h)) (fun h ↦ hb (Fin.ext h))
        (Fin.ext (by omega))
  constructor
  · obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, hq₁, hq₂, h₁, h₂, hne⟩ :=
      hh 0 1 (by decide) (by decide)
    exact ⟨p₁, q₁, p₂, q₂, by simpa [arm_port] using hp₁, by simpa [arm_port] using hp₂,
      hq₁.1, hq₂.1, h₁, h₂, hne⟩
  · obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, hq₁, hq₂, h₁, h₂, hne⟩ :=
      hh 2 3 (by decide) (by decide)
    exact ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, hq₁.2, hq₂.2, h₁, h₂, hne⟩

/-- The prism over the 26-copy chain has no spanning cycle. -/
theorem prism_not_hamiltonian : ¬prism.IsHamiltonian := by
  classical
  intro h
  obtain ⟨C, hle, hham, hc, hcard⟩ := exists_cycle_subgraph h
  have hdeg (p : P) : C.degree p = 2 := by simpa only [ncard_neighborSet] using hcard p
  obtain ⟨k, hclean⟩ := exists_clean_window C hdeg
  refine clean_window_impossible C k hc hclean ?_
  intro i hi
  have hix := i.isLt
  have hk := k.isLt
  let j : Fin 26 := ⟨i.val + 1, by rcases hi with h | ⟨h, h'⟩ <;> omega⟩
  have hj : j.val = i.val + 1 := rfl
  have cl_i (u v : P) (hu : 989 ≤ u.1.val) (hlo : 38 * i.val < v.1.val)
      (hhi : v.1.val < 38 * i.val + 34) : ¬C.Adj u v := by
    apply hclean u v hu
    rcases hi with h | ⟨h, h'⟩ <;> omega
  have cl_j (u v : P) (hu : 989 ≤ u.1.val) (hlo : 38 * j.val < v.1.val)
      (hhi : v.1.val < 38 * j.val + 34) : ¬C.Adj u v := by
    apply hclean u v hu
    rcases hi with h | ⟨h, h'⟩ <;> omega
  have hh (u v : P) (hlo : 38 * i.val + 34 ≤ u.1.val) (hhi : u.1.val ≤ 38 * i.val + 38)
      (hv : 989 ≤ v.1.val) : ¬C.Adj u v := by
    intro hab
    apply hclean v u hv _ hab.symm
    rcases hi with h | ⟨h, h'⟩ <;> omega
  have hL := (outer_contacts C hle hham hc hdeg i cl_i).2
  have hR := (outer_contacts C hle hham hc hdeg j cl_j).1
  have hlabel : 38 * j.val = 38 * i.val + 38 := by omega
  rw [hlabel] at hR
  exact right_barrier PrismLocal.right_coloring C i hle hdeg hc hh hL hR

end Prism8339

namespace Prism8339

private abbrev Local := Fin 41

/-- The local labels 39 and 40 stand for the two global hubs. -/
private def copyVertex (i : Fin 26) (x : Local) : V :=
  ⟨if x.val < 39 then 38 * i.val + x.val else 950 + x.val, by split <;> omega⟩

private theorem copyVertex_val_copy (i : Fin 26) (x : Local) (hx : x.val < 39) :
    (copyVertex i x).val = 38 * i.val + x.val := by
  simp [copyVertex, hx]

private theorem copyVertex_val_hub (i : Fin 26) (x : Local) (hx : 39 ≤ x.val) :
    (copyVertex i x).val = 950 + x.val := by
  simp [copyVertex, show ¬ x.val < 39 by omega]

private theorem copyVertex_injective (i : Fin 26) : Function.Injective (copyVertex i) := by
  intro u v huv
  apply Fin.ext
  have h := congrArg Fin.val huv
  change (if u.val < 39 then 38 * i.val + u.val else 950 + u.val) =
    (if v.val < 39 then 38 * i.val + v.val else 950 + v.val) at h
  split at h <;> split at h <;> omega

/-- Local edges, in increasing order. The test at label 38 uses residue 0. -/
private def LocalAsc (u v : Local) : Prop :=
  u.val < v.val ∧
    ((u.val < 38 ∧ v.val < 39 ∧ (u.val, v.val) ∈ hEdges) ∨
      (u.val < 39 ∧ ((v.val = 39 ∧ u.val % 38 ∈ upper) ∨ (v.val = 40 ∧ u.val % 38 ∈ lower))))

private instance (u v : Local) : Decidable (LocalAsc u v) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

private def LocalAdj (u v : Local) : Prop := LocalAsc u v ∨ LocalAsc v u

private instance (u v : Local) : Decidable (LocalAdj u v) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem graph_adj_of_localAsc (i : Fin 26) {u v : Local} (h : LocalAsc u v) :
    graph.Adj (copyVertex i u) (copyVertex i v) := by
  obtain ⟨huv, hEdge | hHub⟩ := h
  · obtain ⟨hu, hv, he⟩ := hEdge
    have hu' := copyVertex_val_copy i u (by omega)
    have hv' := copyVertex_val_copy i v hv
    have hdiv : (38 * i.val + u.val) / 38 = i.val := by omega
    have hmod : (38 * i.val + u.val) % 38 = u.val := by omega
    have hsub : (38 * i.val + v.val) - 38 * i.val = v.val := by omega
    refine Or.inl ⟨by omega, ?_⟩
    rw [hu', hv', ascAdj, hdiv, hmod, hsub]
    exact Or.inl ⟨i.isLt, he⟩
  · obtain ⟨hu, hSide⟩ := hHub
    have hv : 39 ≤ v.val := by rcases hSide with h | h <;> omega
    have hu' := copyVertex_val_copy i u hu
    have hv' := copyVertex_val_hub i v hv
    have hmod : (38 * i.val + u.val) % 38 = u.val % 38 := by omega
    refine Or.inl ⟨by omega, ?_⟩
    rw [hu', hv', ascAdj, hmod]
    refine Or.inr ⟨by omega, ?_⟩
    rcases hSide with h | h
    · exact Or.inl ⟨by omega, h.2⟩
    · exact Or.inr ⟨by omega, h.2⟩

private theorem graph_adj_of_local (i : Fin 26) {u v : Local} (h : LocalAdj u v) :
    graph.Adj (copyVertex i u) (copyVertex i v) :=
  h.elim (graph_adj_of_localAsc i) (fun h ↦ (graph_adj_of_localAsc i h).symm)

private def IsRoute : Local → List Local → Local → Prop
  | x, [], y => x = y
  | x, z :: zs, y => LocalAdj x z ∧ IsRoute z zs y

private instance routeDecidable : (x : Local) → (p : List Local) → (y : Local) →
    Decidable (IsRoute x p y)
  | x, [], y => inferInstanceAs (Decidable (x = y))
  | x, z :: zs, y =>
    letI := routeDecidable z zs y
    inferInstanceAs (Decidable (LocalAdj x z ∧ IsRoute z zs y))

/-- Route tails, ending at 0, 39 and 40 respectively. The starting vertex is omitted. -/
private def routes : ℕ → List Local × List Local × List Local
  | 0 => ([], [39], [40])
  | 1 => ([0], [2, 3, 4, 17, 39], [40])
  | 2 => ([1, 0], [3, 4, 17, 39], [40])
  | 3 => ([4, 0], [8, 17, 39], [40])
  | 4 => ([0], [17, 39], [3, 40])
  | 5 => ([3, 4, 0], [6, 7, 17, 39], [40])
  | 6 => ([5, 3, 4, 0], [7, 17, 39], [40])
  | 7 => ([8, 3, 4, 0], [17, 39], [40])
  | 8 => ([3, 4, 0], [17, 39], [7, 40])
  | 9 => ([0], [39], [10, 11, 12, 17, 40])
  | 10 => ([9, 0], [39], [11, 12, 17, 40])
  | 11 => ([12, 0], [39], [16, 17, 40])
  | 12 => ([0], [11, 39], [17, 40])
  | 13 => ([11, 12, 0], [39], [14, 15, 17, 40])
  | 14 => ([13, 11, 12, 0], [39], [15, 17, 40])
  | 15 => ([16, 11, 12, 0], [39], [17, 40])
  | 16 => ([11, 12, 0], [15, 39], [17, 40])
  | 17 => ([4, 0], [39], [40])
  | 18 => ([17, 4, 0], [19, 39], [23, 22, 34, 40])
  | 19 => ([17, 4, 0], [39], [18, 23, 22, 34, 40])
  | 20 => ([19, 17, 4, 0], [39], [21, 23, 22, 34, 40])
  | 21 => ([20, 19, 17, 4, 0], [39], [23, 22, 34, 40])
  | 22 => ([17, 4, 0], [23, 39], [34, 40])
  | 23 => ([18, 17, 4, 0], [39], [22, 34, 40])
  | 24 => ([23, 22, 17, 4, 0], [39], [25, 34, 40])
  | 25 => ([24, 23, 22, 17, 4, 0], [39], [34, 40])
  | 26 => ([17, 4, 0], [31, 30, 34, 39], [27, 40])
  | 27 => ([17, 4, 0], [26, 31, 30, 34, 39], [40])
  | 28 => ([27, 17, 4, 0], [29, 31, 30, 34, 39], [40])
  | 29 => ([28, 27, 17, 4, 0], [31, 30, 34, 39], [40])
  | 30 => ([17, 4, 0], [34, 39], [31, 40])
  | 31 => ([26, 17, 4, 0], [30, 34, 39], [40])
  | 32 => ([31, 30, 17, 4, 0], [33, 34, 39], [40])
  | 33 => ([32, 31, 30, 17, 4, 0], [34, 39], [40])
  | 34 => ([30, 17, 4, 0], [39], [40])
  | 35 => ([34, 30, 17, 4, 0], [39], [38, 40])
  | 36 => ([34, 30, 17, 4, 0], [37, 38, 39], [40])
  | 37 => ([36, 34, 30, 17, 4, 0], [38, 39], [40])
  | 38 => ([35, 34, 30, 17, 4, 0], [39], [40])
  | 39 => ([0], [], [17, 40])
  | 40 => ([0], [17, 39], [])
  | _ => ([], [], [])

private abbrev DisjointTails (p q : List Local) : Prop :=
  p.all (fun v ↦ decide (v ∉ q)) = true

private def ValidRoutes (x : Local) : Prop :=
  let t := routes x.val
  IsRoute x t.1 0 ∧ IsRoute x t.2.1 39 ∧ IsRoute x t.2.2 40 ∧
    DisjointTails t.1 t.2.1 ∧ DisjointTails t.1 t.2.2 ∧ DisjointTails t.2.1 t.2.2

private instance (x : Local) : Decidable (ValidRoutes x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private theorem validRoutes : ∀ x : Local, ValidRoutes x := by decide

private theorem one_survives {S : Finset V} (hS : S.card < 3) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : a ∉ S ∨ b ∉ S ∨ c ∉ S := by
  by_contra! h
  have hsub : ({a, b, c} : Finset V) ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  exact (by omega : ¬ ({a, b, c} : Finset V).card ≤ S.card) (Finset.card_le_card hsub)

private theorem one_local_survives {S : Finset V} (hS : S.card < 3) (i : Fin 26)
    {a b c : Local} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    copyVertex i a ∉ S ∨ copyVertex i b ∉ S ∨ copyVertex i c ∉ S :=
  one_survives hS ((copyVertex_injective i).ne hab) ((copyVertex_injective i).ne hac)
    ((copyVertex_injective i).ne hbc)

private theorem ne_of_disjoint {p q : List Local} (h : DisjointTails p q) {a b : Local}
    (ha : a ∈ p) (hb : b ∈ q) : a ≠ b := by
  rintro rfl
  exact of_decide_eq_true (List.all_eq_true.mp h a ha) hb

private theorem surviving_tail {S : Finset V} (hS : S.card < 3) (i : Fin 26)
    {p q r : List Local} (hpq : DisjointTails p q) (hpr : DisjointTails p r)
    (hqr : DisjointTails q r) :
    (∀ v ∈ p, copyVertex i v ∉ S) ∨ (∀ v ∈ q, copyVertex i v ∉ S) ∨
      (∀ v ∈ r, copyVertex i v ∉ S) := by
  by_contra! h
  obtain ⟨⟨a, ha, haS⟩, ⟨b, hb, hbS⟩, ⟨c, hc, hcS⟩⟩ := h
  rcases one_local_survives hS i (ne_of_disjoint hpq ha hb) (ne_of_disjoint hpr ha hc)
      (ne_of_disjoint hqr hb hc) with hs | hs | hs
  · exact hs haS
  · exact hs hbS
  · exact hs hcS

private abbrev remaining (S : Finset V) := graph.induce (S : Set V)ᶜ

private abbrev Survivor (S : Finset V) := ↥((S : Set V)ᶜ)

private theorem edge_reachable {S : Finset V} (i : Fin 26) {x y : Local}
    (hx : copyVertex i x ∉ S) (hy : copyVertex i y ∉ S) (h : LocalAdj x y) :
    (remaining S).Reachable ⟨copyVertex i x, hx⟩ ⟨copyVertex i y, hy⟩ :=
  (SimpleGraph.induce_adj.mpr (graph_adj_of_local i h)).reachable

private theorem route_reachable {S : Finset V} (i : Fin 26) {x y : Local} {p : List Local}
    (hr : IsRoute x p y) (hx : copyVertex i x ∉ S) (hp : ∀ z ∈ p, copyVertex i z ∉ S) :
    ∃ hy : copyVertex i y ∉ S,
      (remaining S).Reachable ⟨copyVertex i x, hx⟩ ⟨copyVertex i y, hy⟩ := by
  induction p generalizing x with
  | nil =>
    have hxy : x = y := hr
    subst y
    exact ⟨hx, .rfl⟩
  | cons z zs ih =>
    obtain ⟨hxz, hrest⟩ : LocalAdj x z ∧ IsRoute z zs y := hr
    have hz := hp z (by simp)
    obtain ⟨hy, hre⟩ := ih hrest hz (fun v hv ↦ hp v (List.mem_cons_of_mem _ hv))
    exact ⟨hy, (edge_reachable i hx hz hxz).trans hre⟩

private abbrev IsAnchor (x : Local) : Prop := x = 0 ∨ x = 39 ∨ x = 40

private theorem reaches_anchor {S : Finset V} (hS : S.card < 3) (i : Fin 26) (x : Local)
    (hx : copyVertex i x ∉ S) :
    ∃ (a : Local) (ha : copyVertex i a ∉ S), IsAnchor a ∧
      (remaining S).Reachable ⟨copyVertex i x, hx⟩ ⟨copyVertex i a, ha⟩ := by
  obtain ⟨hp, hq, hr, hpq, hpr, hqr⟩ := validRoutes x
  rcases surviving_tail hS i hpq hpr hqr with h | h | h
  · obtain ⟨ha, hre⟩ := route_reachable i hp hx h
    exact ⟨0, ha, Or.inl rfl, hre⟩
  · obtain ⟨ha, hre⟩ := route_reachable i hq hx h
    exact ⟨39, ha, Or.inr (Or.inl rfl), hre⟩
  · obtain ⟨ha, hre⟩ := route_reachable i hr hx h
    exact ⟨40, ha, Or.inr (Or.inr rfl), hre⟩

private theorem hubs_reachable {S : Finset V} (hS : S.card < 3) (i : Fin 26)
    (hu : copyVertex i 39 ∉ S) (hl : copyVertex i 40 ∉ S) :
    (remaining S).Reachable ⟨copyVertex i 39, hu⟩ ⟨copyVertex i 40, hl⟩ := by
  rcases one_local_survives hS i (a := 0) (b := 17) (c := 34)
      (by decide) (by decide) (by decide) with h | h | h
  · exact (edge_reachable i hu h (by decide)).trans (edge_reachable i h hl (by decide))
  · exact (edge_reachable i hu h (by decide)).trans (edge_reachable i h hl (by decide))
  · exact (edge_reachable i hu h (by decide)).trans (edge_reachable i h hl (by decide))

private theorem anchors_reachable {S : Finset V} (hS : S.card < 3) (i : Fin 26) {u v : Local}
    (hu : copyVertex i u ∉ S) (hv : copyVertex i v ∉ S) (hu' : IsAnchor u) (hv' : IsAnchor v) :
    (remaining S).Reachable ⟨copyVertex i u, hu⟩ ⟨copyVertex i v, hv⟩ := by
  rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
  all_goals first
    | exact .rfl
    | exact edge_reachable i hu hv (by decide)
    | exact hubs_reachable hS i hu hv
    | exact (hubs_reachable hS i hv hu).symm

private theorem copy_reachable {S : Finset V} (hS : S.card < 3) (i : Fin 26) (x y : Local)
    (hx : copyVertex i x ∉ S) (hy : copyVertex i y ∉ S) :
    (remaining S).Reachable ⟨copyVertex i x, hx⟩ ⟨copyVertex i y, hy⟩ := by
  obtain ⟨a, ha, ha', hxa⟩ := reaches_anchor hS i x hx
  obtain ⟨b, hb, hb', hyb⟩ := reaches_anchor hS i y hy
  exact hxa.trans ((anchors_reachable hS i ha hb ha' hb').trans hyb.symm)

private theorem successive_common {S : Finset V} (hS : S.card < 3) (n : ℕ) (hn : n + 1 < 26) :
    ∃ (u v : Local) (hu : copyVertex ⟨n, by omega⟩ u ∉ S)
      (hv : copyVertex ⟨n + 1, hn⟩ v ∉ S),
      (⟨copyVertex ⟨n, by omega⟩ u, hu⟩ : Survivor S) =
        ⟨copyVertex ⟨n + 1, hn⟩ v, hv⟩ := by
  let i : Fin 26 := ⟨n, by omega⟩
  let j : Fin 26 := ⟨n + 1, hn⟩
  have hJoint : copyVertex i 38 = copyVertex j 0 := by
    apply Fin.ext
    simp only [copyVertex_val_copy _ _ (by decide : (38 : Local).val < 39),
      copyVertex_val_copy _ _ (by decide : (0 : Local).val < 39)]
    change 38 * n + 38 = 38 * (n + 1) + 0
    omega
  rcases one_local_survives hS i (a := 38) (b := 39) (c := 40)
      (by decide) (by decide) (by decide) with h | h | h
  · exact ⟨38, 0, h, hJoint ▸ h, Subtype.ext hJoint⟩
  · exact ⟨39, 39, h, h, rfl⟩
  · exact ⟨40, 40, h, h, rfl⟩

private theorem covered (x : V) : ∃ (i : Fin 26) (v : Local), copyVertex i v = x := by
  by_cases h : x.val < 988
  · refine ⟨⟨x.val / 38, by omega⟩, ⟨x.val % 38, by omega⟩, Fin.ext ?_⟩
    rw [copyVertex_val_copy _ _ (by change x.val % 38 < 39; omega)]
    change 38 * (x.val / 38) + x.val % 38 = x.val
    omega
  · let v : Local := ⟨x.val - 950, by omega⟩
    refine ⟨25, v, Fin.ext ?_⟩
    by_cases h' : v.val < 39
    · rw [copyVertex_val_copy _ _ h']
      change 950 + (x.val - 950) = x.val
      omega
    · rw [copyVertex_val_hub _ _ (by omega : 39 ≤ v.val)]
      change 950 + (x.val - 950) = x.val
      omega

private theorem reachable_from_first {S : Finset V} (hS : S.card < 3) (x : Local)
    (hx : copyVertex 0 x ∉ S) (n : ℕ) (hn : n < 26) (y : Local)
    (hy : copyVertex ⟨n, hn⟩ y ∉ S) :
    (remaining S).Reachable ⟨copyVertex 0 x, hx⟩ ⟨copyVertex ⟨n, hn⟩ y, hy⟩ := by
  induction n generalizing y with
  | zero => exact copy_reachable hS 0 x y hx hy
  | succ n ih =>
    obtain ⟨u, v, hu, hv, hEq⟩ := successive_common hS n hn
    have hxu := ih (by omega) u hu
    rw [hEq] at hxu
    exact hxu.trans (copy_reachable hS ⟨n + 1, hn⟩ v y hv hy)

/-- The graph of the 26-copy chain with both hubs is 3-vertex-connected. -/
theorem graph_connected : graph.IsVertexConnected 3 := by
  refine ⟨?_, fun S hS ↦ ?_⟩
  · rw [Fintype.card_fin]
    decide
  suffices ∃ z : Survivor S, ∀ w : Survivor S, (remaining S).Reachable z w by
    obtain ⟨z, hz⟩ := this
    exact SimpleGraph.Connected.mk (nonempty := ⟨z⟩) fun u v ↦ (hz u).symm.trans (hz v)
  have hroot : ∃ x : Local, copyVertex 0 x ∉ S := by
    rcases one_local_survives hS 0 (a := 0) (b := 39) (c := 40)
        (by decide) (by decide) (by decide) with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨39, h⟩
    · exact ⟨40, h⟩
  obtain ⟨x, hx⟩ := hroot
  refine ⟨⟨copyVertex 0 x, hx⟩, ?_⟩
  rintro ⟨w, hw⟩
  obtain ⟨i, y, rfl⟩ := covered w
  exact reachable_from_first hS x hx i.val i.isLt y hw

end Prism8339

namespace Prism8339

open SimpleGraph

private abbrev Pt := ℝ × ℝ

/-- A line cut takes affine combinations on a segment to the same combinations of its values. -/
private def IsCut (l : Pt → ℝ) : Prop :=
  ∀ a b (t : ℝ), l (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)) =
    (1 - t) * l a + t * l b

private theorem IsCut.smul {l : Pt → ℝ} (hl : IsCut l) (s : ℝ) :
    IsCut (fun p ↦ s * l p) := by
  intro a b t
  dsimp only
  rw [hl]
  ring

private theorem cut_interp {l : Pt → ℝ} (hl : IsCut l) {a b p : Pt} {t : ℝ}
    (hx : p.1 = a.1 + t * (b.1 - a.1)) (hy : p.2 = a.2 + t * (b.2 - a.2)) :
    l p = (1 - t) * l a + t * l b := by
  rw [show p = (_, _) from Prod.ext hx hy, hl]

private theorem cut_nonneg {l : Pt → ℝ} (hl : IsCut l) {a b p : Pt}
    (hp : p ∈ Segment a b) (ha : 0 ≤ l a) (hb : 0 ≤ l b) : 0 ≤ l p := by
  obtain ⟨t, ht, ht', hx, hy⟩ := hp
  rw [cut_interp hl hx hy]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht') ha) (mul_nonneg ht hb)

private theorem cut_zero_endpoint {l : Pt → ℝ} (hl : IsCut l) {a b p : Pt}
    (hp : p ∈ Segment a b) (ha : 0 ≤ l a) (hb : 0 ≤ l b)
    (hpos : 0 < l a ∨ 0 < l b) (hz : l p = 0) :
    (p = a ∧ l a = 0) ∨ (p = b ∧ l b = 0) := by
  obtain ⟨t, ht, ht', hx, hy⟩ := hp
  have hlp := cut_interp hl hx hy
  by_cases h0 : t = 0
  · have hpa : p = a := Prod.ext (by simpa [h0] using hx) (by simpa [h0] using hy)
    exact Or.inl ⟨hpa, hpa ▸ hz⟩
  by_cases h1 : t = 1
  · have hpb : p = b := Prod.ext (by simpa [h1] using hx) (by simpa [h1] using hy)
    exact Or.inr ⟨hpb, hpb ▸ hz⟩
  exfalso
  have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
  have ht1 : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht' h1)
  rcases hpos with ha' | hb'
  · linarith [mul_pos ht1 ha', mul_nonneg ht hb]
  · linarith [mul_nonneg ht1.le ha, mul_pos ht0 hb']

private def CrossFree (a b c d : Pt) : Prop :=
  ∀ ⦃p⦄, p ∈ Segment a b → p ∈ Segment c d →
    (p = a ∨ p = b) ∧ (p = c ∨ p = d)

private theorem segment_swap (a b : Pt) : Segment a b = Segment b a := by
  ext p
  constructor <;> rintro ⟨t, ht, ht', hx, hy⟩ <;>
    exact ⟨1 - t, by linarith, by linarith, by rw [hx]; ring, by rw [hy]; ring⟩

private theorem CrossFree.swap {a b c d : Pt} (h : CrossFree a b c d) :
    CrossFree c d a b := by
  intro p hp hq
  exact (h hq hp).symm

private theorem CrossFree.flip {a b c d : Pt} (h : CrossFree a b c d) :
    CrossFree b a c d := by
  intro p hp hq
  rw [segment_swap b a] at hp
  exact ⟨(h hp hq).1.symm, (h hp hq).2⟩

/-- A cut with a strict value at one endpoint of each edge separates the two edges. -/
private theorem separate {l : Pt → ℝ} (hl : IsCut l) {a b c d : Pt}
    (ha : 0 ≤ l a) (hb : 0 ≤ l b) (hc : l c ≤ 0) (hd : l d ≤ 0)
    (hab : 0 < l a ∨ 0 < l b) (hcd : l c < 0 ∨ l d < 0) : CrossFree a b c d := by
  intro p hp hq
  have hn := hl.smul (-1)
  have hc' : 0 ≤ -1 * l c := by linarith
  have hd' : 0 ≤ -1 * l d := by linarith
  have hcd' : 0 < -1 * l c ∨ 0 < -1 * l d := by rcases hcd with h | h <;> simp [h]
  have h₁ := cut_nonneg hl hp ha hb
  have h₂ := cut_nonneg hn hq hc' hd'
  change 0 ≤ -1 * l p at h₂
  have hz : l p = 0 := by linarith
  exact ⟨(cut_zero_endpoint hl hp ha hb hab hz).imp And.left And.left,
    (cut_zero_endpoint hn hq hc' hd' hcd' (by simp [hz])).imp And.left And.left⟩

/-- If the first edge lies on the cut, the second may touch it only at shared endpoints. -/
private theorem support {l : Pt → ℝ} (hl : IsCut l) {a b c d : Pt}
    (ha : l a = 0) (hb : l b = 0)
    (hc : c = a ∨ c = b ∨ 0 < l c) (hd : d = a ∨ d = b ∨ 0 < l d)
    (hpos : 0 < l c ∨ 0 < l d) : CrossFree a b c d := by
  intro p hp hq
  obtain ⟨t, -, -, hx, hy⟩ := hp
  have hz : l p = 0 := by simp [cut_interp hl hx hy, ha, hb]
  have nonneg {x : Pt} (h : x = a ∨ x = b ∨ 0 < l x) : 0 ≤ l x := by
    rcases h with rfl | rfl | h
    · simp [ha]
    · simp [hb]
    · exact h.le
  have common {x : Pt} (h : x = a ∨ x = b ∨ 0 < l x) (h0 : l x = 0) : x = a ∨ x = b := by
    rcases h with rfl | rfl | h <;> simp_all
  rcases cut_zero_endpoint hl hq (nonneg hc) (nonneg hd) hpos hz with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · exact ⟨common hc h0, Or.inl rfl⟩
  · exact ⟨common hd h0, Or.inr rfl⟩

/-- Signed area of the parallelogram based at `a` with sides `b - a` and `p - a`. -/
private def side (a b p : Pt) : ℝ :=
  (b.1 - a.1) * (p.2 - a.2) - (b.2 - a.2) * (p.1 - a.1)

private theorem side_cut (a b : Pt) : IsCut (side a b) := by
  intro c d t
  unfold side
  dsimp
  ring

private theorem side_left (a b : Pt) : side a b a = 0 := by simp [side]

private theorem side_right (a b : Pt) : side a b b = 0 := by simp [side, mul_comm]

private theorem side_swap (a b p : Pt) : side b a p = -side a b p := by
  unfold side
  ring

/-- Integer coordinates within one copy of `H`. The two end sites are `(0,0)` and `(400,0)`. -/
private def coord : ℕ → ℕ × ℤ
  | 0 => (0, 0)
  | 1 => (20, -19)
  | 2 => (40, -28)
  | 3 => (60, -27)
  | 4 => (50, -6)
  | 5 => (80, -40)
  | 6 => (100, -39)
  | 7 => (120, -28)
  | 8 => (110, -17)
  | 9 => (21, 24)
  | 10 => (41, 30)
  | 11 => (61, 31)
  | 12 => (51, 12)
  | 13 => (81, 43)
  | 14 => (101, 44)
  | 15 => (121, 30)
  | 16 => (111, 21)
  | 17 => (160, 0)
  | 18 => (209, 23)
  | 19 => (199, 34)
  | 20 => (219, 40)
  | 21 => (239, 41)
  | 22 => (269, 12)
  | 23 => (259, 33)
  | 24 => (279, 34)
  | 25 => (299, 20)
  | 26 => (210, -19)
  | 27 => (200, -28)
  | 28 => (220, -37)
  | 29 => (240, -36)
  | 30 => (270, -10)
  | 31 => (260, -29)
  | 32 => (280, -28)
  | 33 => (300, -17)
  | 34 => (320, 0)
  | 35 => (360, 30)
  | 36 => (340, -19)
  | 37 => (380, -28)
  | 38 => (400, 0)
  | _ => (0, 0)

private def lx (j : ℕ) : ℕ := (coord j).1
private def ly (j : ℕ) : ℤ := (coord j).2

private def idet (a b p : ℕ) : ℤ :=
  ((lx b : ℤ) - lx a) * (ly p - ly a) - (ly b - ly a) * ((lx p : ℤ) - lx a)

private def hEdgeOK (e : ℕ × ℕ) : Bool := decide (e.1 < e.2 ∧ e.2 < 39)

private theorem hEdge_bounds (e : ℕ × ℕ) (he : e ∈ hEdges) : e.1 < e.2 ∧ e.2 < 39 := by
  have h : hEdges.all hEdgeOK = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

private theorem lx_bound (j : ℕ) (hj : j < 38) : lx j < 400 := by
  have h : (List.range 38).all (fun k ↦ decide (lx k < 400)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h j (List.mem_range.mpr hj))

private theorem ly_bounds (j : ℕ) (hj : j < 38) : -50 ≤ ly j ∧ ly j ≤ 50 := by
  have h : (List.range 38).all (fun k ↦ decide (-50 ≤ ly k ∧ ly k ≤ 50)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h j (List.mem_range.mpr hj))

private theorem lx_inj (j k : ℕ) (hj : j < 38) (hk : k < 38) (hjk : lx j = lx k) : j = k := by
  have h : (List.range 38).all (fun s ↦ (List.range 38).all
      (fun t ↦ decide (lx s = lx t → s = t))) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp h j (List.mem_range.mpr hj)) k (List.mem_range.mpr hk)) hjk

private def localSupport (a b c d : ℕ) (s : ℤ) : Prop :=
  (c = a ∨ c = b ∨ 0 < s * idet a b c) ∧
  (d = a ∨ d = b ∨ 0 < s * idet a b d) ∧
  (0 < s * idet a b c ∨ 0 < s * idet a b d)

private instance (a b c d : ℕ) (s : ℤ) : Decidable (localSupport a b c d s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private def localSeparate (e f : ℕ × ℕ) : Prop :=
  e = f ∨
  localSupport e.1 e.2 f.1 f.2 1 ∨ localSupport e.1 e.2 f.1 f.2 (-1) ∨
  localSupport f.1 f.2 e.1 e.2 1 ∨ localSupport f.1 f.2 e.1 e.2 (-1)

private instance (e f : ℕ × ℕ) : Decidable (localSeparate e f) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

set_option maxRecDepth 10000 in
private theorem local_certificate (e f : ℕ × ℕ) (he : e ∈ hEdges) (hf : f ∈ hEdges) :
    localSeparate e f := by
  have h : hEdges.all (fun g ↦ hEdges.all (fun k ↦ decide (localSeparate g k))) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h e he) f hf)

private def exterior (up : Bool) : List ℕ := if up then upper else lower
private def sign (up : Bool) : ℤ := if up then 1 else -1
private def S (up : Bool) : ℝ := sign up

private theorem exterior_height (up : Bool) (j : ℕ) (hj : j ∈ exterior up) :
    0 ≤ sign up * ly j := by
  have h : (exterior up).all (fun k ↦ decide (0 ≤ sign up * ly k)) = true := by
    cases up <;> decide
  exact of_decide_eq_true (List.all_eq_true.mp h j hj)

private def between (a b p : ℕ) : Prop :=
  min (lx a) (lx b) < lx p ∧ lx p < max (lx a) (lx b)

private instance (a b p : ℕ) : Decidable (between a b p) := inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 10000 in
private theorem exterior_certificate (up : Bool) (e : ℕ × ℕ) (j : ℕ)
    (he : e ∈ hEdges) (hj : j ∈ exterior up) (hj' : between e.1 e.2 j) :
    0 < sign up * ((lx e.2 : ℤ) - lx e.1) * idet e.1 e.2 j := by
  have h : hEdges.all (fun f ↦ (exterior up).all (fun k ↦ decide (between f.1 f.2 k →
      0 < sign up * ((lx f.2 : ℤ) - lx f.1) * idet f.1 f.2 k))) = true := by
    cases up <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h e he) j hj) hj'

private def px (i j : ℕ) : ℕ := 400 * i + lx j
private def placed (i j : ℕ) : Pt := (px i j, ly j)
private def band (u : V) : ℕ := u.val / 38
private def label (u : V) : ℕ := u.val % 38
private def vx (u : V) : ℕ := px (band u) (label u)
private def site (u : V) : Pt := placed (band u) (label u)

private theorem placed_x (i j : ℕ) : (placed i j).1 = 400 * (i : ℝ) + (lx j : ℝ) := by
  simp [placed, px]

private theorem placed_side (i a b c : ℕ) :
    side (placed i a) (placed i b) (placed i c) = (idet a b c : ℝ) := by
  simp only [side, placed_x, idet, show ∀ j, (placed i j).2 = (ly j : ℝ) by intros; rfl]
  push_cast
  ring

private theorem placed_lt {i a b : ℕ} (h : (placed i a).1 < (placed i b).1) : lx a < lx b := by
  simp only [placed_x, add_lt_add_iff_left, Nat.cast_lt] at h
  exact h

private theorem px_box (i j : ℕ) (hj : j < 39) :
    400 * i ≤ px i j ∧ px i j ≤ 400 * (i + 1) := by
  have h : lx j ≤ 400 := by
    by_cases h' : j < 38
    · exact (lx_bound j h').le
    · have : j = 38 := by omega
      subst j
      decide
  unfold px
  omega

private theorem label_lt (u : V) : label u < 38 := Nat.mod_lt _ (by decide)

private theorem vx_box (u : V) : 400 * band u ≤ vx u ∧ vx u < 400 * (band u + 1) := by
  have := lx_bound (label u) (label_lt u)
  unfold vx px
  omega

private theorem vx_inj : Function.Injective vx := by
  intro u v huv
  have hu := vx_box u
  have hv := vx_box v
  have hb : band u = band v := by omega
  have hcoord : lx (label u) = lx (label v) := by
    unfold vx px at huv
    omega
  have hlabel := lx_inj _ _ (label_lt u) (label_lt v) hcoord
  apply Fin.ext
  unfold band at hb
  unfold label at hlabel
  omega

private theorem site_x_inj {u v : V} (h : (site u).1 = (site v).1) : u = v := by
  apply vx_inj
  change (vx u : ℝ) = (vx v : ℝ) at h
  exact_mod_cast h

private theorem site_gap {u v : V} (h : (site u).1 < (site v).1) :
    (site u).1 + 1 ≤ (site v).1 := by
  change (vx u : ℝ) < (vx v : ℝ) at h
  have h' : vx u < vx v := by exact_mod_cast h
  change (vx u : ℝ) + 1 ≤ (vx v : ℝ)
  exact_mod_cast Nat.succ_le_of_lt h'

private theorem site_atCopy (i : Fin 26) (j : Fin 39) :
    site (atCopy i j) = placed i.val j.val := by
  unfold site band label
  simp only [val_atCopy]
  have hj := j.isLt
  by_cases h : j.val < 38
  · rw [show (38 * i.val + j.val) / 38 = i.val by omega,
      show (38 * i.val + j.val) % 38 = j.val by omega]
  · have hj' : j.val = 38 := by omega
    rw [hj', show (38 * i.val + 38) / 38 = i.val + 1 by omega,
      show (38 * i.val + 38) % 38 = 0 by omega]
    apply Prod.ext
    · simp [placed_x, lx, coord]
      ring
    · rfl

private def hub (up : Bool) : Pt := (0, S up * 10000000)
private def apex (up : Bool) : V := if up then 989 else 990

private def drawing (u : V) : Pt := if u.val ≤ 988 then site u else hub (decide (u.val = 989))

private theorem atCopy_le (i : Fin 26) (j : Fin 39) : (atCopy i j).val ≤ 988 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [val_atCopy]
  omega

private theorem drawing_atCopy (i : Fin 26) (j : Fin 39) :
    drawing (atCopy i j) = placed i.val j.val := by
  rw [drawing, ite_eq_left (atCopy_le i j), site_atCopy]

private theorem drawing_apex (up : Bool) : drawing (apex up) = hub up := by
  cases up <;> rfl

private theorem vertex_kind (u : V) : u.val ≤ 988 ∨ ∃ up, u = apex up := by
  have hu := u.isLt
  by_cases h : u.val ≤ 988
  · exact Or.inl h
  by_cases h' : u.val = 989
  · exact Or.inr ⟨true, Fin.ext h'⟩
  · exact Or.inr ⟨false, Fin.ext (by change u.val = 990; omega)⟩

private structure Small (p : Pt) : Prop where
  xlo : 0 ≤ p.1
  xhi : p.1 ≤ 10800
  ylo : -50 ≤ p.2
  yhi : p.2 ≤ 50

private theorem site_small (u : V) : Small (site u) := by
  have hu : band u ≤ 26 := by
    have := u.isLt
    unfold band
    omega
  have hx : vx u ≤ 10800 := by have := vx_box u; omega
  have hy := ly_bounds _ (label_lt u)
  refine ⟨by change (0 : ℝ) ≤ (vx u : ℝ); positivity, ?_, ?_, ?_⟩
  · change (vx u : ℝ) ≤ 10800
    exact_mod_cast hx
  · change (-50 : ℝ) ≤ (ly (label u) : ℝ)
    exact_mod_cast hy.1
  · change (ly (label u) : ℝ) ≤ 50
    exact_mod_cast hy.2

private theorem site_ne_hub (u : V) (up : Bool) : site u ≠ hub up := by
  intro h
  have hy := congrArg Prod.snd h
  have hs := site_small u
  have h₁ := hs.ylo
  have h₂ := hs.yhi
  cases up <;> norm_num [hub, S, sign] at hy <;> linarith

private theorem drawing_inj : Function.Injective drawing := by
  intro u v h
  rcases vertex_kind u with hu | ⟨up, rfl⟩ <;> rcases vertex_kind v with hv | ⟨vp, rfl⟩
  · rw [drawing, ite_eq_left hu, drawing, ite_eq_left hv] at h
    exact site_x_inj (congrArg Prod.fst h)
  · rw [drawing, ite_eq_left hu, drawing_apex] at h
    exact (site_ne_hub u vp h).elim
  · rw [drawing_apex, drawing, ite_eq_left hv] at h
    exact (site_ne_hub v up h.symm).elim
  · rw [drawing_apex, drawing_apex] at h
    have hs := congrArg Prod.snd h
    cases up <;> cases vp <;> first | rfl | norm_num [hub, S, sign] at hs

private theorem support_local (i a b c d : ℕ) (s : ℤ) (h : localSupport a b c d s) :
    CrossFree (placed i a) (placed i b) (placed i c) (placed i d) := by
  let l : Pt → ℝ := fun p ↦ (s : ℝ) * side (placed i a) (placed i b) p
  have hcast {k : ℕ} (hk : 0 < s * idet a b k) : 0 < l (placed i k) := by
    dsimp only [l]
    rw [placed_side]
    exact_mod_cast hk
  have hEnd {k : ℕ} (hk : k = a ∨ k = b ∨ 0 < s * idet a b k) :
      placed i k = placed i a ∨ placed i k = placed i b ∨ 0 < l (placed i k) := by
    rcases hk with rfl | rfl | hpos
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (hcast hpos))
  exact support ((side_cut _ _).smul _) (by simp [side_left])
    (by simp [side_right]) (hEnd h.1) (hEnd h.2.1) (h.2.2.imp hcast hcast)

private theorem same_copy (i : Fin 26) (a b c d : Fin 39)
    (he : (a.val, b.val) ∈ hEdges) (hf : (c.val, d.val) ∈ hEdges)
    (hne : ({atCopy i a, atCopy i b} : Set V) ≠ {atCopy i c, atCopy i d}) :
    CrossFree (placed i.val a.val) (placed i.val b.val)
      (placed i.val c.val) (placed i.val d.val) := by
  rcases local_certificate _ _ he hf with heq | h | h | h | h
  · have ha : a = c := Fin.ext (congrArg Prod.fst heq)
    have hb : b = d := Fin.ext (congrArg Prod.snd heq)
    exact (hne (by rw [ha, hb])).elim
  · exact support_local _ _ _ _ _ _ h
  · exact support_local _ _ _ _ _ _ h
  · exact (support_local _ _ _ _ _ _ h).swap
  · exact (support_local _ _ _ _ _ _ h).swap

private theorem atCopy_ne (i : Fin 26) {a b : Fin 39} (he : (a.val, b.val) ∈ hEdges) :
    atCopy i a ≠ atCopy i b := by
  have := (hEdge_bounds _ he).1
  intro h
  have h' := congrArg Fin.val h
  simp only [val_atCopy] at h'
  omega

private theorem different_copies (i k : Fin 26) (a b c d : Fin 39)
    (he : (a.val, b.val) ∈ hEdges) (hf : (c.val, d.val) ∈ hEdges) (hik : i.val < k.val) :
    CrossFree (placed i.val a.val) (placed i.val b.val)
      (placed k.val c.val) (placed k.val d.val) := by
  let l : Pt → ℝ := fun p ↦ ((400 * (i.val + 1) : ℕ) : ℝ) - p.1
  have hl : IsCut l := by intro p q t; dsimp [l]; ring
  have hleft (j : Fin 39) : 0 ≤ l (placed i.val j.val) := by
    apply sub_nonneg.mpr
    change (px i.val j.val : ℝ) ≤ ((400 * (i.val + 1) : ℕ) : ℝ)
    exact_mod_cast (px_box i.val j.val j.isLt).2
  have hright (j : Fin 39) : l (placed k.val j.val) ≤ 0 := by
    apply sub_nonpos.mpr
    change ((400 * (i.val + 1) : ℕ) : ℝ) ≤ (px k.val j.val : ℝ)
    exact_mod_cast (show 400 * (i.val + 1) ≤ px k.val j.val from by
      have := (px_box k.val j.val j.isLt).1
      omega)
  refine separate hl (hleft a) (hleft b) (hright c) (hright d) ?_ ?_
  · by_contra! h
    apply atCopy_ne i he
    apply site_x_inj
    rw [site_atCopy, site_atCopy]
    have ha := hleft a
    have hb := hleft b
    dsimp only [l] at ha hb h
    linarith [h.1, h.2]
  · by_contra! h
    apply atCopy_ne k hf
    apply site_x_inj
    rw [site_atCopy, site_atCopy]
    have hc := hright c
    have hd := hright d
    dsimp only [l] at hc hd h
    linarith [h.1, h.2]

private theorem signed_y_diff (up : Bool) {a b : Pt} (ha : Small a) (hb : Small b) :
    -100 ≤ S up * (b.2 - a.2) := by
  have ⟨_, _, ha₁, ha₂⟩ := ha
  have ⟨_, _, hb₁, hb₂⟩ := hb
  cases up <;> simp [S, sign] <;> linarith

private theorem height_gap (up : Bool) {a : Pt} (ha : Small a) :
    9999950 ≤ 10000000 - S up * a.2 := by
  have ⟨_, _, ha₁, ha₂⟩ := ha
  cases up <;> simp [S, sign] <;> linarith

private theorem gap_dominates {dx height span delta : ℝ}
    (hdx : 1 ≤ dx) (hh : 9999950 ≤ height) (hs0 : 0 ≤ span) (hs : span ≤ 10800)
    (hd : -100 ≤ delta) : 0 < dx * height + span * delta := by
  have h₁ := mul_nonneg (show 0 ≤ dx - 1 by linarith) (show 0 ≤ height by linarith)
  have h₂ := mul_nonneg hs0 (show 0 ≤ delta + 100 by linarith)
  nlinarith only [h₁, h₂, hh, hs]

/-- A near-vertical cut through an exterior site and its corresponding apex. -/
private def fanCut (up : Bool) (a p : Pt) : ℝ :=
  (10000000 - S up * a.2) * (p.1 - a.1) + a.1 * (S up * (p.2 - a.2))

private theorem fanCut_cut (up : Bool) (a : Pt) : IsCut (fanCut up a) := by
  intro c d t
  dsimp [fanCut]
  ring

private theorem fanCut_self (up : Bool) (a : Pt) : fanCut up a a = 0 := by simp [fanCut]

private theorem fanCut_hub (up : Bool) (a : Pt) : fanCut up a (hub up) = 0 := by
  cases up <;> simp [fanCut, hub, S, sign] <;> ring

private theorem fanCut_swap (up : Bool) (a b : Pt) : fanCut up a b = -fanCut up b a := by
  unfold fanCut
  ring

private theorem fanCut_pos (up : Bool) (a b : V) (h : (site a).1 < (site b).1) :
    0 < fanCut up (site a) (site b) := by
  have ha := site_small a
  have hb := site_small b
  have hgap : 1 ≤ (site b).1 - (site a).1 := by linarith [site_gap h]
  unfold fanCut
  rw [mul_comm (10000000 - S up * (site a).2)]
  exact gap_dominates hgap (height_gap up ha) ha.xlo ha.xhi (signed_y_diff up ha hb)

private theorem fan_signed_pos (up dir : Bool) (a b : V)
    (h : 0 < S dir * ((site b).1 - (site a).1)) :
    0 < S dir * fanCut up (site a) (site b) := by
  cases dir
  · have hab : (site b).1 < (site a).1 := by simp [S, sign] at h; linarith
    simpa [S, sign, fanCut_swap up (site a) (site b)] using fanCut_pos up b a hab
  · have hab : (site a).1 < (site b).1 := by simp [S, sign] at h; linarith
    simpa [S, sign] using fanCut_pos up a b hab

private theorem fan_outside (up dir : Bool) (u a b : V) (hne : a ≠ b)
    (ha : 0 ≤ S dir * ((site a).1 - (site u).1))
    (hb : 0 ≤ S dir * ((site b).1 - (site u).1)) :
    CrossFree (site u) (hub up) (site a) (site b) := by
  let l : Pt → ℝ := fun p ↦ S dir * fanCut up (site u) p
  have hZ {v : V} (h : S dir * ((site v).1 - (site u).1) = 0) : v = u := by
    apply site_x_inj
    have h' : (site v).1 - (site u).1 = 0 := by
      rcases mul_eq_zero.mp h with hs | hs
      · cases dir <;> norm_num [S, sign] at hs
      · exact hs
    linarith
  have hEnd {v : V} (h : 0 ≤ S dir * ((site v).1 - (site u).1)) :
      site v = site u ∨ site v = hub up ∨ 0 < l (site v) := by
    rcases eq_or_lt_of_le h with hz | hpos
    · exact Or.inl (congrArg site (hZ hz.symm))
    · exact Or.inr (Or.inr (fan_signed_pos up dir u v hpos))
  have hStrict : 0 < l (site a) ∨ 0 < l (site b) := by
    rcases eq_or_lt_of_le ha with hz | ha'
    · rcases eq_or_lt_of_le hb with hw | hb'
      · exact (hne ((hZ hz.symm).trans (hZ hw.symm).symm)).elim
      · exact Or.inr (fan_signed_pos up dir u b hb')
    · exact Or.inl (fan_signed_pos up dir u a ha')
  exact support ((fanCut_cut up _).smul _) (by simp [fanCut_self])
    (by simp [fanCut_hub]) (hEnd ha) (hEnd hb) hStrict

private theorem hub_side_ordered (up : Bool) (a b : V) (hab : (site a).1 < (site b).1) :
    0 < S up * side (site a) (site b) (hub up) := by
  have ha := site_small a
  have hb := site_small b
  have hgap : 1 ≤ (site b).1 - (site a).1 := by linarith [site_gap hab]
  have hs : S up * ((hub up).2 - (site a).2) = 10000000 - S up * (site a).2 := by
    cases up <;> norm_num [hub, S, sign]; ring
  have heq : S up * side (site a) (site b) (hub up) =
      ((site b).1 - (site a).1) * (S up * ((hub up).2 - (site a).2)) +
        (site a).1 * (S up * ((site b).2 - (site a).2)) := by
    simp only [side, show (hub up).1 = 0 from rfl]
    ring
  rw [heq, hs]
  exact gap_dominates hgap (height_gap up ha) ha.xlo ha.xhi (signed_y_diff up ha hb)

private theorem hub_signed (up : Bool) (a b : V) (hne : a ≠ b) :
    0 < S up * ((site b).1 - (site a).1) * side (site a) (site b) (hub up) := by
  rcases lt_or_gt_of_ne (fun h ↦ hne (site_x_inj h)) with h | h
  · calc
      0 < ((site b).1 - (site a).1) * (S up * side (site a) (site b) (hub up)) :=
        mul_pos (sub_pos.mpr h) (hub_side_ordered up a b h)
      _ = _ := by ring
  · rw [side_swap (site b) (site a)]
    calc
      0 < ((site a).1 - (site b).1) * (S up * side (site b) (site a) (hub up)) :=
        mul_pos (sub_pos.mpr h) (hub_side_ordered up b a h)
      _ = _ := by ring

private theorem x_within_band (u : V) (i : Fin 26) (a b : Fin 39)
    (hl : min (placed i.val a.val).1 (placed i.val b.val).1 < (site u).1)
    (hr : (site u).1 < max (placed i.val a.val).1 (placed i.val b.val).1) : band u = i.val := by
  have hleft (j : Fin 39) : ((400 * i.val : ℕ) : ℝ) ≤ (placed i.val j.val).1 := by
    change ((400 * i.val : ℕ) : ℝ) ≤ (px i.val j.val : ℝ)
    exact_mod_cast (px_box i.val j.val j.isLt).1
  have hright (j : Fin 39) : (placed i.val j.val).1 ≤ ((400 * (i.val + 1) : ℕ) : ℝ) := by
    change (px i.val j.val : ℝ) ≤ ((400 * (i.val + 1) : ℕ) : ℝ)
    exact_mod_cast (px_box i.val j.val j.isLt).2
  have hl' : 400 * i.val < vx u := by
    have h : ((400 * i.val : ℕ) : ℝ) < (vx u : ℝ) := lt_of_le_of_lt
      (le_min (hleft a) (hleft b)) hl
    exact_mod_cast h
  have hr' : vx u < 400 * (i.val + 1) := by
    have h : (vx u : ℝ) < ((400 * (i.val + 1) : ℕ) : ℝ) := lt_of_lt_of_le hr
      (max_le (hright a) (hright b))
    exact_mod_cast h
  have := vx_box u
  omega

private theorem fan_inside (up : Bool) (u : V) (i : Fin 26) (a b : Fin 39)
    (he : (a.val, b.val) ∈ hEdges) (hu : label u ∈ exterior up)
    (hl : min (placed i.val a.val).1 (placed i.val b.val).1 < (site u).1)
    (hr : (site u).1 < max (placed i.val a.val).1 (placed i.val b.val).1) :
    CrossFree (site u) (hub up) (placed i.val a.val) (placed i.val b.val) := by
  have hsite : site u = placed i.val (label u) := by rw [site, x_within_band u i a b hl hr]
  have hbetween : between a.val b.val (label u) := by
    rw [hsite, min_lt_iff] at hl
    rw [hsite, lt_max_iff] at hr
    exact ⟨min_lt_iff.mpr (hl.imp placed_lt placed_lt),
      lt_max_iff.mpr (hr.imp placed_lt placed_lt)⟩
  let A := placed i.val a.val
  let B := placed i.val b.val
  let l : Pt → ℝ := fun p ↦ S up * (B.1 - A.1) * side A B p
  have hpos : 0 < l (site u) := by
    dsimp only [l, A, B]
    rw [hsite, placed_side]
    have hdx : B.1 - A.1 = (((lx b.val : ℤ) - lx a.val : ℤ) : ℝ) := by
      simp only [A, B, placed_x]
      push_cast
      ring
    change 0 < S up * (B.1 - A.1) * (idet a.val b.val (label u) : ℝ)
    rw [hdx]
    unfold S
    exact_mod_cast exterior_certificate up (a.val, b.val) (label u) he hu hbetween
  have hHub : 0 < l (hub up) := by
    dsimp only [l, A, B]
    rw [← site_atCopy i a, ← site_atCopy i b]
    exact hub_signed up _ _ (atCopy_ne i he)
  have hFree : CrossFree A B (site u) (hub up) := by
    exact support ((side_cut _ _).smul _) (by simp [side_left]) (by simp [side_right])
      (Or.inr (Or.inr hpos)) (Or.inr (Or.inr hHub)) (Or.inl hpos)
  exact hFree.swap

private theorem fan_chain (up : Bool) (u : V) (i : Fin 26) (a b : Fin 39)
    (he : (a.val, b.val) ∈ hEdges) (hu : label u ∈ exterior up) :
    CrossFree (site u) (hub up) (placed i.val a.val) (placed i.val b.val) := by
  by_cases hl : (site u).1 ≤ min (placed i.val a.val).1 (placed i.val b.val).1
  · rw [← site_atCopy i a, ← site_atCopy i b] at hl ⊢
    exact fan_outside up true u _ _ (atCopy_ne i he)
      (by simpa [S, sign] using sub_nonneg.mpr (le_min_iff.mp hl).1)
      (by simpa [S, sign] using sub_nonneg.mpr (le_min_iff.mp hl).2)
  by_cases hr : max (placed i.val a.val).1 (placed i.val b.val).1 ≤ (site u).1
  · rw [← site_atCopy i a, ← site_atCopy i b] at hr ⊢
    exact fan_outside up false u _ _ (atCopy_ne i he)
      (by simpa [S, sign] using neg_nonneg.mpr (sub_nonpos.mpr (max_le_iff.mp hr).1))
      (by simpa [S, sign] using neg_nonneg.mpr (sub_nonpos.mpr (max_le_iff.mp hr).2))
  exact fan_inside up u i a b he hu (lt_of_not_ge hl) (lt_of_not_ge hr)

private theorem same_fan (up : Bool) (u v : V) (hne : u ≠ v) :
    CrossFree (site u) (hub up) (site v) (hub up) := by
  rcases lt_or_gt_of_ne (fun h ↦ hne (site_x_inj h)) with h | h
  · have hp := fanCut_pos up u v h
    exact support (fanCut_cut up _) (fanCut_self up _) (fanCut_hub up _)
      (Or.inr (Or.inr hp)) (Or.inr (Or.inl rfl)) (Or.inl hp)
  · have hp := fanCut_pos up v u h
    exact (support (fanCut_cut up _) (fanCut_self up _) (fanCut_hub up _)
      (Or.inr (Or.inr hp)) (Or.inr (Or.inl rfl)) (Or.inl hp)).swap

private theorem site_above (u : V) (hu : label u ∈ exterior true) : 0 ≤ (site u).2 := by
  have h : 0 ≤ ly (label u) := by simpa [sign] using exterior_height true (label u) hu
  change (0 : ℝ) ≤ (ly (label u) : ℝ)
  exact_mod_cast h

private theorem site_below (u : V) (hu : label u ∈ exterior false) : (site u).2 ≤ 0 := by
  have h : ly (label u) ≤ 0 := by simpa [sign] using exterior_height false (label u) hu
  change (ly (label u) : ℝ) ≤ 0
  exact_mod_cast h

private theorem opposite_fans (u v : V) (hu : label u ∈ exterior true)
    (hv : label v ∈ exterior false) : CrossFree (site u) (hub true) (site v) (hub false) := by
  have hl : IsCut (Prod.snd : Pt → ℝ) := by intro a b t; dsimp; ring
  have ht : 0 < (hub true).2 := by norm_num [hub, S, sign]
  have hf : (hub false).2 < 0 := by norm_num [hub, S, sign]
  exact separate hl (site_above u hu) ht.le (site_below v hv) hf.le (Or.inr ht) (Or.inr hf)

private def CopyEdge (u v : V) : Prop :=
  ∃ (i : Fin 26) (a b : Fin 39), (a.val, b.val) ∈ hEdges ∧ u = atCopy i a ∧ v = atCopy i b

private def FanEdge (u v : V) : Prop :=
  ∃ up : Bool, u.val ≤ 988 ∧ label u ∈ exterior up ∧ v = apex up

private theorem asc_edge {u v : V} (hlt : u.val < v.val) (h : ascAdj u.val v.val) :
    CopyEdge u v ∨ FanEdge u v := by
  rcases h with ⟨hi, hm⟩ | ⟨hu, hv | hv⟩
  · let i : Fin 26 := ⟨band u, hi⟩
    let a : Fin 39 := ⟨label u, (label_lt u).trans (by decide)⟩
    let d := v.val - 38 * band u
    have hd : d < 39 := (hEdge_bounds (label u, d) hm).2
    let b : Fin 39 := ⟨d, hd⟩
    refine Or.inl ⟨i, a, b, hm, Fin.ext ?_, Fin.ext ?_⟩
    · simp only [val_atCopy, i, a]
      unfold band label
      omega
    · simp only [val_atCopy, i, b, d]
      unfold band
      omega
  · exact Or.inr ⟨true, hu, hv.2, Fin.ext hv.1⟩
  · exact Or.inr ⟨false, hu, hv.2, Fin.ext hv.1⟩

private theorem asc_crossFree {u v x y : V} (huv : u.val < v.val) (hxy : x.val < y.val)
    (hadjU : ascAdj u.val v.val) (hadjX : ascAdj x.val y.val)
    (hne : ({u, v} : Set V) ≠ {x, y}) :
    CrossFree (drawing u) (drawing v) (drawing x) (drawing y) := by
  rcases asc_edge huv hadjU with ⟨i, a, b, he, rfl, rfl⟩ | ⟨up, hu, he, rfl⟩ <;>
    rcases asc_edge hxy hadjX with ⟨k, c, d, hf, rfl, rfl⟩ | ⟨vp, hx, hf, rfl⟩
  · simp only [drawing_atCopy]
    rcases lt_trichotomy i.val k.val with hik | hik | hik
    · exact different_copies i k a b c d he hf hik
    · obtain rfl : i = k := Fin.ext hik
      exact same_copy i a b c d he hf hne
    · exact (different_copies k i c d a b hf he hik).swap
  · rw [drawing_atCopy, drawing_atCopy, drawing_apex, drawing, ite_eq_left hx]
    exact (fan_chain vp x i a b he hf).swap
  · rw [drawing_apex, drawing, ite_eq_left hu, drawing_atCopy, drawing_atCopy]
    exact fan_chain up u k c d hf he
  · rw [drawing_apex, drawing_apex, drawing, ite_eq_left hu, drawing, ite_eq_left hx]
    by_cases h : up = vp
    · subst vp
      apply same_fan
      intro huv'
      exact hne (by rw [huv'])
    · cases up <;> cases vp
      · exact (h rfl).elim
      · exact (opposite_fans x u hf he).swap
      · exact opposite_fans u x he hf
      · exact (h rfl).elim

private theorem drawing_crossFree {u v x y : V} (huv : graph.Adj u v) (hxy : graph.Adj x y)
    (hne : ({u, v} : Set V) ≠ {x, y}) :
    CrossFree (drawing u) (drawing v) (drawing x) (drawing y) := by
  change (_ ∧ _) ∨ (_ ∧ _) at huv hxy
  rcases huv with huv | hvu <;> rcases hxy with hxy | hyx
  · exact asc_crossFree huv.1 hxy.1 huv.2 hxy.2 hne
  · rw [Set.pair_comm x y] at hne
    exact (asc_crossFree huv.1 hyx.1 huv.2 hyx.2 hne).swap.flip.swap
  · rw [Set.pair_comm u v] at hne
    exact (asc_crossFree hvu.1 hxy.1 hvu.2 hxy.2 hne).flip
  · rw [Set.pair_comm u v, Set.pair_comm x y] at hne
    exact (asc_crossFree hvu.1 hyx.1 hvu.2 hyx.2 hne).flip.swap.flip.swap

/-- Špacapan's chained graph `G₍₂₆₎` is planar in the straight-line sense. -/
theorem graph_planar : graph.IsPlanar := by
  refine Or.inr ⟨drawing, drawing_inj, ?_, ?_⟩
  · intro u v hadj heq
    exact graph.ne_of_adj hadj (drawing_inj heq)
  · intro u v x y huv hxy hne p hp
    exact drawing_crossFree huv hxy hne hp.1 hp.2

end Prism8339

@[expose] public section

namespace MathlibExt.Combinatorics.PlanarGraphPrismHamiltonicityWanted

/-! Source record `OPG-47285`. -/

/-- **Prism-Hamiltonicity conjecture for 3-connected planar graphs.** For every finite simple
graph $G$ that is $3$-vertex-connected and straight-line planar, the prism
$G \mathbin{\square} K_2$, the Cartesian product of $G$ with the complete graph on two
vertices, is Hamiltonian. -/
def conjecture : Prop :=
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    SimpleGraph.IsVertexConnected 3 G → SimpleGraph.IsPlanar G →
      (G □ SimpleGraph.completeGraph (Fin 2)).IsHamiltonian

/--
**Špacapan's counterexample to prism-Hamiltonicity.** The prism-Hamiltonicity conjecture for
3-connected planar graphs is false: there is a finite simple graph $G$ that is
$3$-vertex-connected and straight-line planar whose prism $G \mathbin{\square} K_2$ is not
Hamiltonian.

Source: S. Špacapan, A counterexample to prism-hamiltonicity
of 3-connected planar graphs, Journal of Combinatorial Theory, Series B 146 (2021), 364–371,
https://doi.org/10.1016/j.jctb.2020.09.012; arXiv version: https://arxiv.org/abs/1906.06683. Moved from
`OpenConjectures/Combinatorics/PlanarGraphPrismHamiltonicity`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  exact Prism8339.prism_not_hamiltonian <|
    h Prism8339.V inferInstance inferInstance Prism8339.graph inferInstance
      Prism8339.graph_connected Prism8339.graph_planar

end MathlibExt.Combinatorics.PlanarGraphPrismHamiltonicityWanted
