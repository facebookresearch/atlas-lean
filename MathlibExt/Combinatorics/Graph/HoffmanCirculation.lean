/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith

/-!
# Hoffman's bounded circulation theorem

A. Schrijver, [*A Course in Combinatorial Optimization*](https://homepages.cwi.nl/~lex/files/dict.pdf)
(23 March 2017), §4.5, pp. 69–70, Theorems 4.6–4.7, gives the cut criterion for a bounded
circulation and existence of an integral circulation for integral bounds. The version with
prescribed net inflows extends that criterion.

We use a different proof: fix the value on one arc `i → j` at a time. Each cut
containing `j` but not `i` imposes a lower bound on the value; a cut containing
`i` but not `j` imposes an upper bound. Taking the union and intersection of the
two cuts shows that these bounds are compatible. Only finite maxima, addition and subtraction
are needed, so the same selection argument works over both `ℝ` and `ℤ`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

variable {V E : Type*} [DecidableEq V]

/-- Arc IDs entering `S` from its complement. -/
def enteringArcs [Fintype E] (tail head : E → V) (S : Finset V) : Finset E :=
  Finset.univ.filter fun e => tail e ∉ S ∧ head e ∈ S

/-- Arc IDs leaving `S` for its complement. -/
def leavingArcs [Fintype E] (tail head : E → V) (S : Finset V) : Finset E :=
  Finset.univ.filter fun e => tail e ∈ S ∧ head e ∉ S

/-- A flow within the (possibly signed) bounds `d, c` and with net inflow `b`
at every vertex. A circulation is the case `b = 0`. -/
def IsBoundedFlow [Fintype V] [Fintype E] [DecidableEq E] (tail head : E → V)
    (d c : E → ℝ) (b : V → ℝ) (f : E → ℝ) : Prop :=
  d ≤ f ∧ f ≤ c ∧ (incidenceMatrix tail head).mulVec f = b

/-- The upper bound on the net flow into a cut contributed by one arc `i → j`. -/
private def term {R : Type*} [Zero R] [Sub R] (i j : V) (d c : R) (X : Finset V) : R :=
  (if i ∉ X ∧ j ∈ X then c else 0) - (if i ∈ X ∧ j ∉ X then d else 0)

private lemma sum_term {R : Type*} [AddCommGroup R] [Fintype E] (tail head : E → V)
    (d c : E → R) (X : Finset V) :
    ∑ e, term (tail e) (head e) (d e) (c e) X =
      (∑ e ∈ enteringArcs tail head X, c e) - ∑ e ∈ leavingArcs tail head X, d e := by
  simp [term, enteringArcs, leavingArcs, Finset.sum_filter, Finset.sum_sub_distrib]

section Selection

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

private lemma term_submodular (i j : V) {d c : R} (hdc : d ≤ c) (X Y : Finset V) :
    term i j d c (X ∪ Y) + term i j d c (X ∩ Y) ≤ term i j d c X + term i j d c Y := by
  by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;> by_cases hi' : i ∈ Y <;> by_cases hj' : j ∈ Y <;>
    simp [term, hi, hj, hi', hj'] <;> linarith

private def Supermodular (p : Finset V → R) : Prop :=
  ∀ X Y, p X + p Y ≤ p (X ∪ Y) + p (X ∩ Y)

/-- With all other arcs removed from the cut inequalities, the remaining deficit
`p` is supermodular. Pick the largest lower bound imposed on the arc `i → j`. -/
private lemma fix_arc [Finite V] (i j : V) {d c : R} (hdc : d ≤ c)
    (p : Finset V → R) (hp : Supermodular p) (h : ∀ X, p X ≤ term i j d c X) :
    ∃ z, d ≤ z ∧ z ≤ c ∧ ∀ X, p X ≤ term i j z z X := by
  classical
  let _ := Fintype.ofFinite V
  let lower (X : Finset V) := if i ∉ X ∧ j ∈ X then max d (p X) else d
  obtain ⟨A, -, hA⟩ := Finset.univ.exists_max_image lower Finset.univ_nonempty
  have hlow (X) : lower X ≤ lower A := hA X (Finset.mem_univ _)
  refine ⟨lower A, ?_, ?_, ?_⟩
  · simp [lower, apply_ite (d ≤ ·)]
  · by_cases ha : i ∉ A ∧ j ∈ A
    · simp only [lower, ite_eq_left ha, max_le_iff]
      exact ⟨hdc, by simpa [term, ha.1, ha.2] using h A⟩
    · simpa [lower, ha] using hdc
  intro X
  by_cases hin : i ∉ X ∧ j ∈ X
  · simpa [term, hin.1, hin.2] using (le_max_right d (p X)).trans
      (by simpa [lower, hin] using hlow X : max d (p X) ≤ lower A)
  by_cases hout : i ∈ X ∧ j ∉ X
  · have hXd : p X ≤ -d := by simpa [term, hout.1, hout.2] using h X
    by_cases ha : i ∉ A ∧ j ∈ A
    · -- Both endpoints are in the union and neither is in the intersection.
      have hU : p (X ∪ A) ≤ 0 := by simpa [term, hout.1, ha.2] using h (X ∪ A)
      have hI : p (X ∩ A) ≤ 0 := by simpa [term, hout.2, ha.1] using h (X ∩ A)
      have hXA := hp X A
      have hle : max d (p A) ≤ -p X := max_le (by linarith) (by linarith)
      simp [term, hout.1, hout.2, lower, ha]
      linarith
    · simpa [term, hout.1, hout.2, lower, ha] using hXd
  · simpa [term, hin, hout] using h X

/-- Eliminate arc IDs one at a time, subtracting each selected arc's net
contribution from the remaining requirement. -/
private lemma select_arcs [Finite V] (tail head : E → V) (d c : E → R)
    (hdc : d ≤ c) (s : Finset E) (p : Finset V → R) (hp : Supermodular p)
    (h : ∀ X, p X ≤ ∑ e ∈ s, term (tail e) (head e) (d e) (c e) X) :
    ∃ f : E → R, (∀ e ∈ s, d e ≤ f e ∧ f e ≤ c e) ∧
      ∀ X, p X ≤ ∑ e ∈ s, term (tail e) (head e) (f e) (f e) X := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => exact ⟨d, by simp, by simpa using h⟩
  | @insert a s ha ih =>
    let C (X) := ∑ e ∈ s, term (tail e) (head e) (d e) (c e) X
    have hC (X Y) : C (X ∪ Y) + C (X ∩ Y) ≤ C X + C Y := by
      simp only [C, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun e _ => term_submodular _ _ (hdc e) X Y
    obtain ⟨z, hdz, hzc, hz⟩ := fix_arc (tail a) (head a) (hdc a) (fun X => p X - C X)
      (fun X Y => by linarith only [hp X Y, hC X Y]) (fun X => by
        have hX := h X
        rw [Finset.sum_insert ha] at hX
        exact sub_le_iff_le_add.mpr hX)
    let t := term (tail a) (head a) z z
    obtain ⟨f, hbox, hf⟩ := ih (fun X => p X - t X)
      (fun X Y => by
        have ht := term_submodular (tail a) (head a) (le_refl z) X Y
        dsimp [t]
        linarith only [hp X Y, ht]) (fun X => by
        change p X - t X ≤ C X
        have hzX : p X - C X ≤ t X := hz X
        linarith)
    let g := Function.update f a z
    have hga : g a = z := Function.update_self ..
    have hgs (e) (he : e ∈ s) : g e = f e :=
      Function.update_of_ne (show e ≠ a from fun heq => ha (heq ▸ he)) ..
    refine ⟨g, ?_, fun X => ?_⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · simpa only [hga] using And.intro hdz hzc
      · simpa only [hgs e he] using hbox e he
    · rw [Finset.sum_insert ha, hga, Finset.sum_congr rfl (fun e he => by rw [hgs e he])]
      exact sub_le_iff_le_add'.mp (hf X)

variable [Finite V] [Fintype E] (tail head : E → V)

private lemma select_flow (d c : E → R) (b : V → R) (hdc : d ≤ c)
    (h : ∀ X, ∑ v ∈ X, b v ≤
      (∑ e ∈ enteringArcs tail head X, c e) - ∑ e ∈ leavingArcs tail head X, d e) :
    ∃ f : E → R, d ≤ f ∧ f ≤ c ∧ ∀ X, ∑ v ∈ X, b v ≤
      (∑ e ∈ enteringArcs tail head X, f e) - ∑ e ∈ leavingArcs tail head X, f e := by
  obtain ⟨f, hbox, hf⟩ := select_arcs tail head d c hdc Finset.univ (fun X => ∑ v ∈ X, b v)
    (fun _ _ => Finset.sum_union_inter.symm.le) (by simpa only [sum_term] using h)
  exact ⟨f, fun e => (hbox e (Finset.mem_univ _)).1, fun e => (hbox e (Finset.mem_univ _)).2,
    by simpa only [sum_term] using hf⟩

end Selection

variable [Fintype V] [Fintype E] [DecidableEq E] {tail head : E → V}

/-- Summing the net inflow over a vertex set counts exactly the entering arcs
positively and the leaving arcs negatively. Internal arcs, including loops, cancel. -/
theorem sum_incidenceMatrix_mulVec_eq_cut (tail head : E → V) (f : E → ℝ) (X : Finset V) :
    ∑ v ∈ X, (incidenceMatrix tail head).mulVec f v =
      (∑ e ∈ enteringArcs tail head X, f e) - ∑ e ∈ leavingArcs tail head X, f e := by
  rw [← sum_term]
  simp only [Matrix.mulVec, dotProduct, incidenceMatrix, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  by_cases hi : tail e ∈ X <;> by_cases hj : head e ∈ X <;> simp [term, hi, hj]

private lemma balance_of_cut_le (b : V → ℝ) (f : E → ℝ) (hb : ∑ v, b v = 0)
    (h : ∀ X, ∑ v ∈ X, b v ≤
      (∑ e ∈ enteringArcs tail head X, f e) - ∑ e ∈ leavingArcs tail head X, f e) :
    (incidenceMatrix tail head).mulVec f = b := by
  have hle (v : V) : b v ≤ (incidenceMatrix tail head).mulVec f v := by
    simpa only [← sum_incidenceMatrix_mulVec_eq_cut, Finset.sum_singleton] using h {v}
  have heq := hb.trans (sum_incidenceMatrix_mulVec_eq_zero tail head f).symm
  exact funext fun v => ((Finset.sum_eq_sum_iff_of_le (fun u _ => hle u)).mp heq v
    (Finset.mem_univ _)).symm

/-- A bounded flow with prescribed net inflows satisfies every directed cut inequality. -/
theorem IsBoundedFlow.cut_le {d c f : E → ℝ} {b : V → ℝ}
    (hf : IsBoundedFlow tail head d c b f) (X : Finset V) :
    ∑ v ∈ X, b v ≤
      (∑ e ∈ enteringArcs tail head X, c e) - ∑ e ∈ leavingArcs tail head X, d e := by
  rw [← hf.2.2, sum_incidenceMatrix_mulVec_eq_cut]
  exact sub_le_sub (Finset.sum_le_sum fun e _ => hf.2.1 e) (Finset.sum_le_sum fun e _ => hf.1 e)

/-- A bounded real flow with prescribed net inflows of total zero exists exactly
when every set's net demand is at most upper capacity entering minus lower capacity leaving. -/
theorem exists_boundedFlow_iff (tail head : E → V) (d c : E → ℝ) (b : V → ℝ)
    (hdc : d ≤ c) (hb : ∑ v, b v = 0) :
    (∃ f, IsBoundedFlow tail head d c b f) ↔ ∀ X, ∑ v ∈ X, b v ≤
      (∑ e ∈ enteringArcs tail head X, c e) - ∑ e ∈ leavingArcs tail head X, d e := by
  refine ⟨fun ⟨_, hf⟩ => hf.cut_le, fun h => ?_⟩
  obtain ⟨f, hdf, hfc, hf⟩ := select_flow tail head d c b hdc h
  exact ⟨f, hdf, hfc, balance_of_cut_le b f hb hf⟩

/-- Hoffman's circulation theorem: for arbitrary real bounds `d ≤ c`, a bounded
circulation exists iff the lower sum entering each set is at most the upper sum leaving it. -/
theorem hoffman_circulation_iff (tail head : E → V) (d c : E → ℝ) (hdc : d ≤ c) :
    (∃ f, IsBoundedFlow tail head d c 0 f) ↔ ∀ X,
      (∑ e ∈ enteringArcs tail head X, d e) ≤ ∑ e ∈ leavingArcs tail head X, c e := by
  rw [exists_boundedFlow_iff tail head d c 0 hdc (by simp)]
  constructor <;> intro h X <;>
    simpa [enteringArcs, leavingArcs, sub_nonneg] using h Xᶜ

/-- With integral bounds and prescribed integral net inflows, existence of a real
bounded flow implies existence of an integer-valued one with those same data. -/
theorem exists_int_boundedFlow (tail head : E → V) (d c : E → ℤ) (b : V → ℤ)
    (h : ∃ f, IsBoundedFlow tail head (fun e => (d e : ℝ)) (fun e => (c e : ℝ))
      (fun v => (b v : ℝ)) f) :
    ∃ g : E → ℤ, IsBoundedFlow tail head (fun e => (d e : ℝ)) (fun e => (c e : ℝ))
      (fun v => (b v : ℝ)) (fun e => (g e : ℝ)) := by
  obtain ⟨f, hf⟩ := h
  have hdc : d ≤ c := fun e => (Int.cast_le (R := ℝ)).mp ((hf.1 e).trans (hf.2.1 e))
  obtain ⟨g, hdg, hgc, hg⟩ := select_flow tail head d c b hdc (fun X => by
    exact_mod_cast hf.cut_le X)
  refine ⟨g, fun e => Int.cast_le.mpr (hdg e), fun e => Int.cast_le.mpr (hgc e), ?_⟩
  apply balance_of_cut_le
  · simpa only [hf.2.2] using sum_incidenceMatrix_mulVec_eq_zero tail head f
  · intro X
    exact_mod_cast hg X

/-- With integral bounds, a real bounded circulation can be replaced by an integer one. -/
theorem exists_int_circulation (tail head : E → V) (d c : E → ℤ)
    (h : ∃ f, IsBoundedFlow tail head (fun e => (d e : ℝ)) (fun e => (c e : ℝ)) 0 f) :
    ∃ g : E → ℤ, IsBoundedFlow tail head (fun e => (d e : ℝ)) (fun e => (c e : ℝ)) 0
      (fun e => (g e : ℝ)) := by
  have hzero : (fun v : V => ((0 : V → ℤ) v : ℝ)) = 0 := by ext; simp
  simpa only [hzero] using exists_int_boundedFlow tail head d c 0 (by rwa [hzero])

end MathlibExt.Combinatorics.Graph.ArcNetwork
