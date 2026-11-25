/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Homomorphism densities, the cut norm and the counting lemma

A *weighted graph* on a finite vertex type `V` (all node weights `1`, edge weights real, loops
allowed) is a function `w : Sym2 V → ℝ`; a simple graph `G` gives the `0`/`1` weight
`adjWeight G`. For a simple graph `F` on a finite type `α`, the *homomorphism density*
`homDensity F w = |V| ^ (-|α|) ∑_{φ : α → V} ∏_{ij ∈ E(F)} w(φ i, φ j)`
is `t(F, G)` of Lovász and Szegedy (*Limits of dense graph sequences*, J. Combin. Theory Ser. B 96
(2006), §2.1), and for `w = adjWeight G` it is the probability that a uniformly random map
`V(F) → V(G)` is a homomorphism.

The *cut norm* of `u : Sym2 V → ℝ` is `|V| ^ (-2) max_{S, T ⊆ V} |∑_{x ∈ S, y ∈ T} u(x, y)|`
(Frieze and Kannan; Lovász–Szegedy, §4.1); the cut distance of two weighted graphs on the same
vertex set is `cutNorm (w - w')`.

The main result is the *counting lemma*: for edge weights in `[0, 1]`,
`|t(F, w) - t(F, w')| ≤ |E(F)| · ‖w - w'‖_□`
(Lovász–Szegedy, Lemma 4.1 and inequality (7); Borgs–Chayes–Lovász–Sós–Vesztergombi,
*Convergent sequences of dense graphs I*, Adv. Math. 219 (2008), Theorem 2.7 (a) with constant 4
for weights in `[-1, 1]`). The proof is the telescoping argument of Lovász–Szegedy: change one edge
weight at a time, and bound each step by the cut norm after integrating out the two endpoints of
that edge.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.GraphLimits

open Finset

variable {α V : Type*}

section Defs

variable [Fintype α] [DecidableEq α] [Fintype V]

/-- **Weight of a map into a weighted graph.** The weight `∏_{ij ∈ E(F)} w(φ i, φ j)` of a map
`φ : α → V` from the vertices of a simple graph `F` to a weighted graph `w : Sym2 V → ℝ`
(Lovász–Szegedy, *Limits of dense graph sequences*, §2.1, `hom_φ(F, G)` with node weights `1`). -/
def homWeight (F : SimpleGraph α) [DecidableRel F.Adj] (w : Sym2 V → ℝ) (φ : α → V) : ℝ :=
  ∏ e ∈ F.edgeFinset, w (e.map φ)

/-- **Homomorphism density.** The density `t(F, w) = |V| ^ (-|V(F)|) ∑_{φ : V(F) → V}
∏_{ij ∈ E(F)} w(φ i, φ j)` of a simple graph `F` on `α` in a weighted graph `w : Sym2 V → ℝ`
with unit node weights (Lovász–Szegedy, *Limits of dense graph sequences*, J. Combin. Theory
Ser. B 96 (2006), §2.1: `t(F, G) = hom(F, G) / α_G ^ k`). For a simple graph `G` on a nonempty
vertex set with weight `adjWeight G` this is the probability that a uniformly random map
`V(F) → V(G)` is a homomorphism. For an empty vertex type `V` there is no map from a nonempty
`α`, and the value is `0` for every `F` with a vertex (`0 / 0`), which is not a probability; the
results that read it as one assume `V` nonempty. -/
noncomputable def homDensity (F : SimpleGraph α) [DecidableRel F.Adj] (w : Sym2 V → ℝ) : ℝ :=
  (∑ φ : α → V, homWeight F w φ) / (Fintype.card V : ℝ) ^ Fintype.card α

end Defs

/-- **Edge weight of a simple graph.** The `0`/`1` weighted graph of a simple graph `G`: weight `1`
on the edges of `G` and `0` on non-edges and loops. -/
def adjWeight (G : SimpleGraph V) [DecidableRel G.Adj] : Sym2 V → ℝ :=
  fun e => if e ∈ G.edgeSet then 1 else 0

/-- **Simple-graph weights lie in the unit interval.** The `0`/`1` weights of a simple graph lie in
`[0, 1]`. -/
theorem adjWeight_mem_unitInterval (G : SimpleGraph V) [DecidableRel G.Adj] (z : Sym2 V) :
    0 ≤ adjWeight G z ∧ adjWeight G z ≤ 1 := by
  unfold adjWeight
  split_ifs <;> norm_num

section CutNorm

variable [Fintype V]

/-- **Unnormalized cut norm.** The quantity `max_{S, T ⊆ V} |∑_{x ∈ S} ∑_{y ∈ T} u(x, y)|` of
`u : Sym2 V → ℝ` (the matrix cut norm `‖A‖_□` of Lovász–Szegedy, §4.1). -/
noncomputable def cutMax (u : Sym2 V → ℝ) : ℝ :=
  (univ : Finset (Finset V × Finset V)).sup' univ_nonempty
    (fun p => |∑ x ∈ p.1, ∑ y ∈ p.2, u s(x, y)|)

/-- **Cut norm.** The cut norm `‖u‖_□ = |V| ^ (-2) max_{S, T ⊆ V} |∑_{x ∈ S, y ∈ T} u(x, y)|` of a
symmetric kernel `u : Sym2 V → ℝ` on a finite vertex type; `cutNorm (w - w')` is the cut (rectangle)
distance `d_□(G, G')` of two weighted graphs on the same vertex set (Frieze–Kannan; Lovász–Szegedy,
*Limits of dense graph sequences*, §4.1; Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences
of dense graphs I*, equation (2.4)). -/
noncomputable def cutNorm (u : Sym2 V → ℝ) : ℝ :=
  cutMax u / (Fintype.card V : ℝ) ^ 2

theorem cutMax_nonneg (u : Sym2 V → ℝ) : 0 ≤ cutMax u :=
  (abs_nonneg _).trans
    (le_sup' (fun p : Finset V × Finset V => |∑ x ∈ p.1, ∑ y ∈ p.2, u s(x, y)|) (mem_univ (∅, ∅)))

/-- **Nonnegativity of the cut norm.** The cut norm of every kernel is nonnegative. -/
theorem cutNorm_nonneg (u : Sym2 V → ℝ) : 0 ≤ cutNorm u :=
  div_nonneg (cutMax_nonneg u) (by positivity)

theorem abs_sum_sum_le_cutMax (u : Sym2 V → ℝ) (S T : Finset V) :
    |∑ x ∈ S, ∑ y ∈ T, u s(x, y)| ≤ cutMax u :=
  le_sup' (fun p : Finset V × Finset V => |∑ x ∈ p.1, ∑ y ∈ p.2, u s(x, y)|) (mem_univ (S, T))

end CutNorm

/-- **Weighted sums are bounded by subset sums.** For weights `a ∈ [0, 1]`, the weighted sum
`∑ a x * g x` is bounded in absolute value by the sum of `g` over some subset (the set where `g`
has the sign of the weighted sum). -/
theorem exists_abs_sum_mul_le {ι : Type*} (s : Finset ι) (a g : ι → ℝ)
    (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1) : ∃ S ⊆ s, |∑ x ∈ s, a x * g x| ≤ |∑ x ∈ S, g x| := by
  classical
  by_cases h : 0 ≤ ∑ x ∈ s, a x * g x
  · refine ⟨s.filter (fun x => 0 < g x), filter_subset _ _, ?_⟩
    rw [abs_of_nonneg h]
    have h1 : ∑ x ∈ s.filter (fun x => ¬ 0 < g x), a x * g x ≤ 0 :=
      sum_nonpos fun x hx =>
        mul_nonpos_of_nonneg_of_nonpos (ha x).1 (not_lt.1 (mem_filter.1 hx).2)
    have h2 : ∑ x ∈ s.filter (fun x => 0 < g x), a x * g x ≤
        ∑ x ∈ s.filter (fun x => 0 < g x), g x :=
      sum_le_sum fun x hx => by
        have := (mem_filter.1 hx).2
        nlinarith [(ha x).2]
    rw [← sum_filter_add_sum_filter_not s (fun x => 0 < g x)]
    linarith [le_abs_self (∑ x ∈ s.filter (fun x => 0 < g x), g x)]
  · rw [not_le] at h
    refine ⟨s.filter (fun x => g x < 0), filter_subset _ _, ?_⟩
    rw [abs_of_neg h]
    have h1 : 0 ≤ ∑ x ∈ s.filter (fun x => ¬ g x < 0), a x * g x :=
      sum_nonneg fun x hx => mul_nonneg (ha x).1 (not_lt.1 (mem_filter.1 hx).2)
    have h2 : ∑ x ∈ s.filter (fun x => g x < 0), g x ≤
        ∑ x ∈ s.filter (fun x => g x < 0), a x * g x :=
      sum_le_sum fun x hx => by
        have := (mem_filter.1 hx).2
        nlinarith [(ha x).2]
    have h3 := sum_filter_add_sum_filter_not s (fun x => g x < 0) (fun x => a x * g x)
    linarith [neg_abs_le (∑ x ∈ s.filter (fun x => g x < 0), g x)]

/-- **Bilinear forms are bounded by the cut norm.** For `a, b : V → [0, 1]`,
`|∑_{x, y} a(x) b(y) u(x, y)| ≤ max_{S, T} |∑_{x ∈ S, y ∈ T} u(x, y)|` (Borgs–Chayes–Lovász–Sós–
Vesztergombi, *Convergent sequences of dense graphs I*, Adv. Math. 219 (2008), equation (3.3),
finite form). -/
theorem abs_sum_sum_mul_le_cutMax [Fintype V] (a b : V → ℝ) (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1)
    (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1) (u : Sym2 V → ℝ) :
    |∑ x, ∑ y, a x * b y * u s(x, y)| ≤ cutMax u := by
  obtain ⟨S, -, hS⟩ := exists_abs_sum_mul_le univ a (fun x => ∑ y, b y * u s(x, y)) ha
  obtain ⟨T, -, hT⟩ := exists_abs_sum_mul_le univ b (fun y => ∑ x ∈ S, u s(x, y)) hb
  have e1 : ∑ x, ∑ y, a x * b y * u s(x, y) = ∑ x, a x * ∑ y, b y * u s(x, y) := by
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun y _ => by ring
  have e2 : ∑ x ∈ S, ∑ y, b y * u s(x, y) = ∑ y, b y * ∑ x ∈ S, u s(x, y) := by
    rw [sum_comm]
    exact sum_congr rfl fun y _ => (mul_sum _ _ _).symm
  calc |∑ x, ∑ y, a x * b y * u s(x, y)| ≤ |∑ x ∈ S, ∑ y, b y * u s(x, y)| := e1 ▸ hS
    _ ≤ |∑ y ∈ T, ∑ x ∈ S, u s(x, y)| := e2 ▸ hT
    _ = |∑ x ∈ S, ∑ y ∈ T, u s(x, y)| := by rw [sum_comm]
    _ ≤ cutMax u := abs_sum_sum_le_cutMax u S T

section Sums

variable [Fintype α] [DecidableEq α] [Fintype V]

-- Re-randomizing one coordinate: `∑_φ ∑_x f(φ[u ↦ x]) = |V| ∑_φ f(φ)`.
theorem sum_sum_update (f : (α → V) → ℝ) (u : α) :
    ∑ φ : α → V, ∑ x : V, f (Function.update φ u x) = Fintype.card V * ∑ φ, f φ := by
  set e := Equiv.funSplitAt u V
  have key : ∀ (y x : V) (r : {j // j ≠ u} → V),
      Function.update (e.symm (y, r)) u x = e.symm (x, r) := by
    intro y x r
    funext j
    by_cases h : j = u
    · subst h; simp [e]
    · simp [e, h]
  rw [sum_comm]
  calc ∑ x, ∑ φ, f (Function.update φ u x)
      = ∑ x, ∑ p : V × ({j // j ≠ u} → V), f (Function.update (e.symm p) u x) :=
        sum_congr rfl fun x _ => (Equiv.sum_comp e.symm (fun φ => f (Function.update φ u x))).symm
    _ = ∑ x, ∑ _y : V, ∑ r, f (e.symm (x, r)) := by
        refine sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type]
        simp only [key]
    _ = ∑ x, (Fintype.card V : ℝ) * ∑ r, f (e.symm (x, r)) := by
        simp [sum_const, card_univ, nsmul_eq_mul]
    _ = Fintype.card V * ∑ p : V × ({j // j ≠ u} → V), f (e.symm p) := by
        rw [Fintype.sum_prod_type, mul_sum]
    _ = Fintype.card V * ∑ φ, f φ := by rw [Equiv.sum_comp e.symm f]

/-- **One telescoping step of the counting lemma.** Integrating out the two endpoints of an edge
`uv` bounds the contribution of a kernel `D` on that edge, multiplied by `[0, 1]`-valued factors on
the other edges, by the cut norm of `D` (Lovász–Szegedy, proof of Lemma 4.1). -/
theorem card_sq_mul_abs_sum_le (E' : Finset (Sym2 α)) {u v : α} (huv : u ≠ v)
    (hE' : ∀ j ∈ E', ¬ j.IsDiag ∧ j ≠ s(u, v)) (k : Sym2 α → Sym2 V → ℝ)
    (hk : ∀ j z, 0 ≤ k j z ∧ k j z ≤ 1) (D : Sym2 V → ℝ) :
    (Fintype.card V : ℝ) ^ 2 * |∑ φ : α → V, D s(φ u, φ v) * ∏ j ∈ E', k j (j.map φ)| ≤
      (Fintype.card V : ℝ) ^ Fintype.card α * cutMax D := by
  set Φ : (α → V) → ℝ := fun φ => D s(φ u, φ v) * ∏ j ∈ E', k j (j.map φ) with hΦ
  have hsum : (Fintype.card V : ℝ) ^ 2 * ∑ φ, Φ φ =
      ∑ φ : α → V, ∑ x : V, ∑ y : V,
        Φ (Function.update (Function.update φ u x) v y) := by
    rw [sum_sum_update (fun ψ => ∑ y : V, Φ (Function.update ψ v y)) u]
    simp only [sum_sum_update Φ v]
    ring
  -- For fixed `φ`, the double sum factors as `C * ∑ x y, A x * B y * D(x, y)`.
  have hfix : ∀ φ : α → V,
      |∑ x : V, ∑ y : V, Φ (Function.update (Function.update φ u x) v y)| ≤ cutMax D := by
    intro φ
    set A : V → ℝ := fun x =>
      ∏ j ∈ E'.filter (fun j => u ∈ j), k j (j.map (Function.update φ u x)) with hA
    set B : V → ℝ := fun y =>
      ∏ j ∈ E'.filter (fun j => u ∉ j ∧ v ∈ j), k j (j.map (Function.update φ v y)) with hB
    set C : ℝ := ∏ j ∈ E'.filter (fun j => u ∉ j ∧ v ∉ j), k j (j.map φ) with hC
    have hA01 : ∀ x, 0 ≤ A x ∧ A x ≤ 1 := fun x =>
      ⟨prod_nonneg fun j _ => (hk _ _).1,
        prod_le_one₀ (fun j _ => (hk _ _).1) fun j _ => (hk _ _).2⟩
    have hB01 : ∀ y, 0 ≤ B y ∧ B y ≤ 1 := fun y =>
      ⟨prod_nonneg fun j _ => (hk _ _).1,
        prod_le_one₀ (fun j _ => (hk _ _).1) fun j _ => (hk _ _).2⟩
    have hC0 : 0 ≤ C := prod_nonneg fun j _ => (hk _ _).1
    have hC1 : C ≤ 1 := prod_le_one₀ (fun j _ => (hk _ _).1) fun j _ => (hk _ _).2
    have hfac : ∀ x y, Φ (Function.update (Function.update φ u x) v y) =
        C * (A x * B y * D s(x, y)) := by
      intro x y
      set ψ := Function.update (Function.update φ u x) v y with hψ
      have hψu : ψ u = x := by
        rw [hψ, Function.update_of_ne huv, Function.update_self]
      have hψv : ψ v = y := by rw [hψ, Function.update_self]
      -- split the product over `E'` into the three groups of edges
      have hsplit : ∏ j ∈ E', k j (j.map ψ) =
          (∏ j ∈ E'.filter (fun j => u ∈ j), k j (j.map ψ)) *
          ((∏ j ∈ E'.filter (fun j => u ∉ j ∧ v ∈ j), k j (j.map ψ)) *
            ∏ j ∈ E'.filter (fun j => u ∉ j ∧ v ∉ j), k j (j.map ψ)) := by
        rw [← prod_filter_mul_prod_filter_not E' (fun j => u ∈ j)]
        congr 1
        rw [← prod_filter_mul_prod_filter_not (E'.filter (fun j => u ∉ j)) (fun j => v ∈ j),
          filter_filter, filter_filter]
      have h1 : ∏ j ∈ E'.filter (fun j => u ∈ j), k j (j.map ψ) = A x := by
        refine prod_congr rfl fun j hj => ?_
        obtain ⟨hjE, hju⟩ := mem_filter.1 hj
        congr 1
        refine Sym2.map_congr fun a ha => ?_
        have hav : a ≠ v := by
          rintro rfl
          obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 hju
          rcases Sym2.mem_iff.1 ha with h | h
          · exact huv h.symm
          · exact (hE' _ hjE).2 (by rw [h])
        rw [hψ, Function.update_of_ne hav]
      have h2 : ∏ j ∈ E'.filter (fun j => u ∉ j ∧ v ∈ j), k j (j.map ψ) = B y := by
        refine prod_congr rfl fun j hj => ?_
        obtain ⟨-, hju, -⟩ := mem_filter.1 hj
        congr 1
        refine Sym2.map_congr fun a ha => ?_
        have hau : a ≠ u := by rintro rfl; exact hju ha
        rw [hψ, Function.update_comm huv, Function.update_of_ne hau]
      have h3 : ∏ j ∈ E'.filter (fun j => u ∉ j ∧ v ∉ j), k j (j.map ψ) = C := by
        refine prod_congr rfl fun j hj => ?_
        obtain ⟨-, hju, hjv⟩ := mem_filter.1 hj
        congr 1
        refine Sym2.map_congr fun a ha => ?_
        have hau : a ≠ u := by rintro rfl; exact hju ha
        have hav : a ≠ v := by rintro rfl; exact hjv ha
        rw [hψ, Function.update_of_ne hav, Function.update_of_ne hau]
      simp only [hΦ]
      rw [hψu, hψv, hsplit, h1, h2, h3]
      ring
    have hrw : ∑ x : V, ∑ y : V, Φ (Function.update (Function.update φ u x) v y) =
        C * ∑ x, ∑ y, A x * B y * D s(x, y) := by
      simp only [hfac, mul_sum]
    rw [hrw, abs_mul, abs_of_nonneg hC0]
    calc C * |∑ x, ∑ y, A x * B y * D s(x, y)| ≤ 1 * cutMax D :=
          mul_le_mul hC1 (abs_sum_sum_mul_le_cutMax A B hA01 hB01 D) (abs_nonneg _) zero_le_one
      _ = cutMax D := one_mul _
  calc (Fintype.card V : ℝ) ^ 2 * |∑ φ, Φ φ| = |(Fintype.card V : ℝ) ^ 2 * ∑ φ, Φ φ| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (Fintype.card V : ℝ))]
    _ = |∑ φ : α → V, ∑ x : V, ∑ y : V, Φ (Function.update (Function.update φ u x) v y)| := by
        rw [hsum]
    _ ≤ ∑ φ : α → V, |∑ x : V, ∑ y : V, Φ (Function.update (Function.update φ u x) v y)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _φ : α → V, cutMax D := sum_le_sum fun φ _ => hfix φ
    _ = (Fintype.card V : ℝ) ^ Fintype.card α * cutMax D := by
        simp [sum_const, card_univ, nsmul_eq_mul]

end Sums

section CountingLemma

variable [Fintype α] [DecidableEq α] [Fintype V]

/-- **Counting lemma.** For a simple graph `F` and two weighted graphs `w, w'` on the same finite
vertex set with edge weights in `[0, 1]`,
`|t(F, w) - t(F, w')| ≤ |E(F)| · ‖w - w'‖_□`, where `‖·‖_□` is the cut norm
(Lovász–Szegedy, *Limits of dense graph sequences*, J. Combin. Theory Ser. B 96 (2006), Lemma 4.1
and inequality (7); compare Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense
graphs I*, Adv. Math. 219 (2008), Theorem 2.7 (a)). -/
theorem abs_homDensity_sub_homDensity_le (F : SimpleGraph α) [DecidableRel F.Adj]
    (w w' : Sym2 V → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hw' : ∀ z, 0 ≤ w' z ∧ w' z ≤ 1) :
    |homDensity F w - homDensity F w'| ≤ F.edgeFinset.card * cutNorm (w - w') := by
  have hR : 0 ≤ (F.edgeFinset.card : ℝ) * cutNorm (w - w') :=
    mul_nonneg (Nat.cast_nonneg _) (cutNorm_nonneg _)
  rcases (Fintype.card V).eq_zero_or_pos with hn | hn
  · -- no vertices: both densities are `0` (if `F` has a vertex) or `1` (if not)
    rcases (Fintype.card α).eq_zero_or_pos with hk | hk
    · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hk
      have hE : F.edgeFinset = ∅ :=
        eq_empty_of_forall_notMem fun e => Sym2.ind (fun a _ => isEmptyElim a) e
      have : homDensity F w = homDensity F w' := by simp [homDensity, homWeight, hE]
      rw [this, sub_self, abs_zero]
      exact hR
    · have : (Fintype.card V : ℝ) ^ Fintype.card α = 0 := by
        rw [hn, Nat.cast_zero, zero_pow hk.ne']
      simp only [homDensity, this, div_zero, sub_self, abs_zero]
      exact hR
  -- the telescoping identity, indexing the edges by `Fin N` to order them
  set E := F.edgeFinset
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hnpos : 0 < n := by rw [hn_def]; exact_mod_cast hn
  set e := Fintype.equivFin (Sym2 α)
  set E' : Finset (Fin (Fintype.card (Sym2 α))) := E.map e.toEmbedding
  -- the factors on the other edges of the `m`-th telescoping term
  set R : Fin (Fintype.card (Sym2 α)) → Finset (Sym2 α) := fun m =>
    (E'.filter (· < m) ∪ E'.filter (m < ·)).map e.symm.toEmbedding with hR_def
  set K : Fin (Fintype.card (Sym2 α)) → Sym2 α → Sym2 V → ℝ := fun m j =>
    if e j < m then w else w' with hK_def
  have hprod : ∀ (f : Sym2 α → ℝ), ∏ i ∈ E, f i = ∏ m ∈ E', f (e.symm m) := by
    intro f
    rw [prod_map]
    simp
  have htel : ∀ φ : α → V, homWeight F w φ - homWeight F w' φ =
      ∑ m ∈ E', (w - w') ((e.symm m).map φ) * ∏ j ∈ R m, K m j (j.map φ) := by
    intro φ
    have h := prod_add_ordered E' (fun m => w' ((e.symm m).map φ))
      (fun m => (w - w') ((e.symm m).map φ))
    simp only [Pi.sub_apply, add_sub_cancel] at h
    simp only [homWeight]
    rw [hprod (fun i => w (i.map φ)), hprod (fun i => w' (i.map φ)), h, add_sub_cancel_left]
    refine sum_congr rfl fun m _ => ?_
    rw [hR_def, prod_map, prod_union (disjoint_filter.2 fun j _ h1 h2 => lt_asymm h1 h2),
      mul_assoc]
    congr 2
    · refine prod_congr rfl fun j hj => ?_
      have hjm : j < m := (mem_filter.1 hj).2
      simp [hK_def, hjm]
    · refine prod_congr rfl fun j hj => ?_
      have hjm : ¬ j < m := not_lt.2 (mem_filter.1 hj).2.le
      simp [hK_def, hjm]
  -- each telescoping term is bounded by the cut norm
  have hterm : ∀ m ∈ E', n ^ 2 * |∑ φ : α → V, (w - w') ((e.symm m).map φ) *
      ∏ j ∈ R m, K m j (j.map φ)| ≤ n ^ Fintype.card α * cutMax (w - w') := by
    intro m hm
    have hiE : e.symm m ∈ E := by
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hm
      simpa using hi
    have hRm : ∀ j ∈ R m, j ∈ E ∧ j ≠ e.symm m := by
      intro j hj
      obtain ⟨j', hj', rfl⟩ := mem_map.1 hj
      have hj'E : j' ∈ E' ∧ j' ≠ m := by
        rcases mem_union.1 hj' with h | h
        · exact ⟨(mem_filter.1 h).1, (mem_filter.1 h).2.ne⟩
        · exact ⟨(mem_filter.1 h).1, (mem_filter.1 h).2.ne'⟩
      refine ⟨?_, fun h => hj'E.2 (e.symm.injective h)⟩
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hj'E.1
      simpa using hi
    have hk : ∀ (j : Sym2 α) (z : Sym2 V), 0 ≤ K m j z ∧ K m j z ≤ 1 := by
      intro j z
      simp only [hK_def]
      split_ifs
      · exact hw z
      · exact hw' z
    revert hiE hRm
    generalize e.symm m = i
    intro hiE hRm
    induction i using Sym2.ind with
    | _ u v =>
    have huv : u ≠ v := fun h => SimpleGraph.not_isDiag_of_mem_edgeSet F
      (SimpleGraph.mem_edgeFinset.1 hiE) (by simp [h])
    have hE'' : ∀ j ∈ R m, ¬ j.IsDiag ∧ j ≠ s(u, v) := fun j hj =>
      ⟨SimpleGraph.not_isDiag_of_mem_edgeSet F (SimpleGraph.mem_edgeFinset.1 (hRm j hj).1),
        (hRm j hj).2⟩
    have := card_sq_mul_abs_sum_le (V := V) (R m) huv hE'' (K m) hk (w - w')
    simpa only [Sym2.map_mk] using this
  have hsum : n ^ 2 * |∑ φ : α → V, (homWeight F w φ - homWeight F w' φ)| ≤
      E.card * (n ^ Fintype.card α * cutMax (w - w')) := by
    simp only [htel]
    rw [sum_comm]
    calc n ^ 2 * |∑ m ∈ E', ∑ φ : α → V, (w - w') ((e.symm m).map φ) *
          ∏ j ∈ R m, K m j (j.map φ)|
        ≤ n ^ 2 * ∑ m ∈ E', |∑ φ : α → V, (w - w') ((e.symm m).map φ) *
          ∏ j ∈ R m, K m j (j.map φ)| :=
          mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
      _ = ∑ m ∈ E', n ^ 2 * |∑ φ : α → V, (w - w') ((e.symm m).map φ) *
          ∏ j ∈ R m, K m j (j.map φ)| := mul_sum _ _ _
      _ ≤ ∑ _m ∈ E', n ^ Fintype.card α * cutMax (w - w') := sum_le_sum hterm
      _ = E.card * (n ^ Fintype.card α * cutMax (w - w')) := by
          rw [sum_const, nsmul_eq_mul, card_map]
  have hnk : 0 < n ^ Fintype.card α := pow_pos hnpos _
  have hdiff : homDensity F w - homDensity F w' =
      (∑ φ : α → V, (homWeight F w φ - homWeight F w' φ)) / n ^ Fintype.card α := by
    simp only [homDensity, sum_sub_distrib, sub_div, hn_def]
  rw [hdiff, abs_div, abs_of_pos hnk, div_le_iff₀ hnk, cutNorm, ← hn_def]
  have hn2 : 0 < n ^ 2 := by positivity
  rw [← mul_le_mul_iff_of_pos_left hn2]
  calc n ^ 2 * |∑ φ : α → V, (homWeight F w φ - homWeight F w' φ)|
      ≤ E.card * (n ^ Fintype.card α * cutMax (w - w')) := hsum
    _ = n ^ 2 * (E.card * (cutMax (w - w') / n ^ 2) * n ^ Fintype.card α) := by
        field_simp

end CountingLemma

section Basic

variable [Fintype α] [DecidableEq α] [Fintype V]

/-- **Homomorphism density counts homomorphisms.** For simple graphs `F` and `G`,
`t(F, G) = hom(F, G) / |V(G)| ^ |V(F)|`, where `hom(F, G)` is the number of graph homomorphisms
`F →g G` (Lovász–Szegedy, *Limits of dense graph sequences*, §2.1: for an unweighted graph `G`,
`t(F, G) = hom(F, G) / |V(G)| ^ |V(F)|`). -/
theorem homDensity_adjWeight (F : SimpleGraph α) [DecidableRel F.Adj] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    homDensity F (adjWeight G) =
      (Nat.card (F →g G) : ℝ) / (Fintype.card V : ℝ) ^ Fintype.card α := by
  classical
  set P : (α → V) → Prop := fun φ => ∀ a b, F.Adj a b → G.Adj (φ a) (φ b) with hP
  have h1 : ∀ φ : α → V, homWeight F (adjWeight G) φ = if P φ then 1 else 0 := by
    intro φ
    simp only [homWeight, adjWeight]
    by_cases hφ : P φ
    · simp only [hφ, ↓reduceIte]
      refine prod_eq_one fun e he => ?_
      induction e using Sym2.ind with
      | _ a b => simp [hφ a b (by simpa using he)]
    · simp only [hφ, ↓reduceIte]
      simp only [hP, not_forall] at hφ
      obtain ⟨a, b, hab, hn⟩ := hφ
      exact prod_eq_zero (i := s(a, b)) (SimpleGraph.mem_edgeFinset.2 ((F.mem_edgeSet).2 hab))
        (by simp [hn])
  have h2 : Nat.card (F →g G) = (univ.filter P).card := by
    have e : (F →g G) ≃ {φ : α → V // P φ} :=
      { toFun := fun f => ⟨f, fun _ _ h => f.map_rel h⟩
        invFun := fun p => ⟨p.1, fun h => p.2 _ _ h⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [homDensity]
  simp only [h1]
  rw [Finset.sum_boole, h2]

/-- **Homomorphism densities are nonnegative.** Densities in a weighted graph with nonnegative
edge weights are nonnegative. -/
theorem homDensity_nonneg (F : SimpleGraph α) [DecidableRel F.Adj] {w : Sym2 V → ℝ}
    (hw : ∀ z, 0 ≤ w z) : 0 ≤ homDensity F w :=
  div_nonneg (sum_nonneg fun _ _ => prod_nonneg fun _ _ => hw _) (by positivity)

/-- **Homomorphism densities are at most one.** Densities in a weighted graph with edge weights
in `[0, 1]` are at most `1`. -/
theorem homDensity_le_one (F : SimpleGraph α) [DecidableRel F.Adj] {w : Sym2 V → ℝ}
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) : homDensity F w ≤ 1 := by
  rcases (Fintype.card V).eq_zero_or_pos with hn | hn
  · rcases (Fintype.card α).eq_zero_or_pos with hk | hk
    · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hk
      have hE : F.edgeFinset = ∅ :=
        eq_empty_of_forall_notMem fun e => Sym2.ind (fun a _ => isEmptyElim a) e
      simp [homDensity, homWeight, hE]
    · simp [homDensity, hn, zero_pow hk.ne']
  have hpos : 0 < (Fintype.card V : ℝ) ^ Fintype.card α := by positivity
  rw [homDensity, div_le_one hpos]
  calc ∑ φ : α → V, homWeight F w φ ≤ ∑ _φ : α → V, (1 : ℝ) :=
        sum_le_sum fun φ _ => prod_le_one₀ (fun _ _ => (hw _).1) fun _ _ => (hw _).2
    _ = (Fintype.card V : ℝ) ^ Fintype.card α := by simp

/-- **Homomorphism densities are normalized.** The density of an edgeless graph in any weighted
graph with a vertex is `1` (homomorphism
densities are *normalized*, Lovász–Szegedy, *Limits of dense graph sequences*, §2.2). -/
theorem homDensity_bot [Nonempty V] (w : Sym2 V → ℝ) :
    homDensity (⊥ : SimpleGraph α) w = 1 := by
  have hpos : 0 < (Fintype.card V : ℝ) ^ Fintype.card α := by
    have := Fintype.card_pos (α := V)
    positivity
  have h1 : ∀ φ : α → V, homWeight (⊥ : SimpleGraph α) w φ = 1 := fun φ =>
    prod_eq_one fun e he => by simp at he
  simp [homDensity, h1, hpos.ne']

end Basic

section PartitionAverage

variable [Fintype V] [DecidableEq V]

/-- **Partition average of a weighted graph.** For a partition `P = {V₁, …, V_k}` of the vertex set,
the weighted graph `G_P` on the same vertices whose weight on `xy` (`x ∈ Vᵢ`, `y ∈ Vⱼ`) is the
average `e_G(Vᵢ, Vⱼ) / (|Vᵢ| |Vⱼ|)` of the weights of `G` over `Vᵢ × Vⱼ` (Borgs–Chayes–Lovász–Sós–
Vesztergombi, *Convergent sequences of dense graphs I*, Adv. Math. 219 (2008), §2.4, with unit
node weights). -/
noncomputable def partitionAverage (P : Finpartition (univ : Finset V)) (w : Sym2 V → ℝ) :
    Sym2 V → ℝ :=
  Sym2.lift ⟨fun x y => (∑ a ∈ P.part x, ∑ b ∈ P.part y, w s(a, b)) /
      (((P.part x).card : ℝ) * (P.part y).card), fun x y => by
    dsimp only
    rw [mul_comm (((P.part x).card : ℝ)), sum_comm]
    congr 1
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by rw [Sym2.eq_swap]⟩

/-- **L² norm of a weighted graph.** The normalized norm
`‖G‖₂ = (|V|⁻² ∑_{x, y} w(x, y)²) ^ (1/2)` of a weighted graph with
unit node weights (Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I*,
§2.1). -/
noncomputable def kernelL2Norm (w : Sym2 V → ℝ) : ℝ :=
  Real.sqrt ((∑ x, ∑ y, w s(x, y) ^ 2) / (Fintype.card V : ℝ) ^ 2)

end PartitionAverage

end MathlibExt.Combinatorics.SimpleGraph.GraphLimits
