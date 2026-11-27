/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three-chromatic (0,2)-graphs
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace MathlibExt.Combinatorics.ThreeChromaticZeroTwoGraphWanted

/-! UnsolvedMath record `OPG-562`.

The problem-page discussion notes that infinite three-chromatic `(0,2)`-graphs
are easy to construct; the open question concerns finite graphs, represented
here by the vertex type `Fin n`.
-/

@[expose] public section

/-- **$(0,2)$-graphs.** For a natural number $n$, a simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ is a $(0,2)$-graph when every two distinct vertices of $G$ have either
exactly zero or exactly two common neighbors. -/
def IsZeroTwo {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, u ≠ v →
    (G.commonNeighbors u v).ncard = 0 ∨
      (G.commonNeighbors u v).ncard = 2

/-- **The three-chromatic $(0,2)$-graph conjecture.** It asserts that there are a natural number
$n$ and a simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ in which every two distinct
vertices have either zero or two common neighbors, such that the chromatic number of $G$ is $3$.
-/
noncomputable def conjecture : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    IsZeroTwo G ∧ G.chromaticNumber = 3

end

variable {n : ℕ} {G : SimpleGraph (Fin n)}

private lemma existsUnique_otherCommonNeighbor (hG : IsZeroTwo G) {a u v : Fin n}
    (huv : u ≠ v) (hua : G.Adj u a) (hva : G.Adj v a) :
    ∃! b, b ≠ a ∧ G.Adj u b ∧ G.Adj v b := by
  have ha : a ∈ G.commonNeighbors u v := G.mem_commonNeighbors.mpr ⟨hua, hva⟩
  have htwo : (G.commonNeighbors u v).ncard = 2 :=
    (hG u v huv).resolve_left (Set.ncard_ne_zero_of_mem ha)
  obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp (show
      (G.commonNeighbors u v \ {a}).ncard = 1 by
    rw [Set.ncard_sdiff_singleton_of_mem ha, htwo])
  have hmem (x : Fin n) : x ∈ G.commonNeighbors u v \ {a} ↔
      x ≠ a ∧ G.Adj u x ∧ G.Adj v x := by
    simp [G.mem_commonNeighbors, and_comm]
  refine ⟨b, (hmem b).mp (by rw [hb]; simp), fun x hx ↦ ?_⟩
  simpa only [hb, Set.mem_singleton_iff] using (hmem x).mpr hx

private abbrev OtherNeighbors (G : SimpleGraph (Fin n)) (u v : Fin n) :=
  {a : Fin n // G.Adj u a ∧ a ≠ v}

private lemma existsUnique_opposite (hG : IsZeroTwo G) {u v : Fin n} (huv : G.Adj u v)
    (a : OtherNeighbors G u v) : ∃! b : OtherNeighbors G v u, G.Adj a.1 b.1 := by
  obtain ⟨b, ⟨hbu, hab, hvb⟩, huniq⟩ :=
    existsUnique_otherCommonNeighbor hG a.2.2 a.2.1.symm huv.symm
  exact ⟨⟨b, hvb, hbu⟩, hab, fun x hx ↦ Subtype.ext (huniq x ⟨x.2.2, hx, x.2.1⟩)⟩

-- Completing a two-edge path to a square gives inverse maps at the two ends of an edge.
private noncomputable def oppositeEquiv (hG : IsZeroTwo G) {u v : Fin n} (huv : G.Adj u v) :
    OtherNeighbors G u v ≃ OtherNeighbors G v u where
  toFun a := (existsUnique_opposite hG huv a).exists.choose
  invFun b := (existsUnique_opposite hG huv.symm b).exists.choose
  left_inv a := by
    dsimp
    have h := (existsUnique_opposite hG huv a).exists.choose_spec
    have h' := existsUnique_opposite hG huv.symm
      (existsUnique_opposite hG huv a).exists.choose
    exact h'.unique h'.exists.choose_spec h.symm
  right_inv b := by
    dsimp
    have h := (existsUnique_opposite hG huv.symm b).exists.choose_spec
    have h' := existsUnique_opposite hG huv
      (existsUnique_opposite hG huv.symm b).exists.choose
    exact h'.unique h'.exists.choose_spec h.symm

private lemma adj_oppositeEquiv (hG : IsZeroTwo G) {u v : Fin n} (huv : G.Adj u v)
    (a : OtherNeighbors G u v) : G.Adj a.1 (oppositeEquiv hG huv a).1 :=
  (existsUnique_opposite hG huv a).exists.choose_spec

open scoped Classical in
private lemma sum_otherNeighbors (w : Fin n → Fin n → ℝ)
    (hsupport : ∀ u v, ¬G.Adj u v → w u v = 0) (u v : Fin n) :
    (∑ a : OtherNeighbors G u v, w u a.1) + w u v = ∑ a, w u a := by
  classical
  rw [← Finset.sum_subtype ((Finset.univ.erase v).filter (G.Adj u)) (by
    intro a
    simp [and_comm]) (w u), Finset.sum_filter]
  convert Finset.sum_erase_add Finset.univ (w u) (Finset.mem_univ v) using 2
  exact Finset.sum_congr rfl fun a _ ↦ by
    by_cases ha : G.Adj u a
    · simp [ha]
    · simp [ha, hsupport u a ha]

-- At a positive maximum W on u → v, square closure would make the sum of the
-- opposite labels exceed the sum of the same number of copies of W by 2W.
private lemma eq_zero_of_squareClosed_of_divergenceFree (hG : IsZeroTwo G)
    (w : Fin n → Fin n → ℝ) (hskew : ∀ u v, w v u = -w u v)
    (hsupport : ∀ u v, ¬G.Adj u v → w u v = 0)
    (hclosed : ∀ u v a b, G.Adj u v → G.Adj v b → G.Adj b a → G.Adj a u →
      w u v + w v b + w b a + w a u = 0)
    (hdiv : ∀ u, ∑ v, w u v = 0) : ∀ u v, w u v = 0 := by
  classical
  by_contra! h
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨x, y, hpos⟩ : ∃ x y, 0 < w x y := by
    rcases lt_or_gt_of_ne hxy with hneg | hpos
    · exact ⟨y, x, by rw [hskew x y]; exact neg_pos.mpr hneg⟩
    · exact ⟨x, y, hpos⟩
  obtain ⟨⟨u, v⟩, -, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin n × Fin n)) (fun p ↦ w p.1 p.2) ⟨(x, y), Finset.mem_univ _⟩
  have hW : 0 < w u v := hpos.trans_le (hmax (x, y) (Finset.mem_univ _))
  have huv : G.Adj u v := by
    by_contra h
    exact hW.ne' (hsupport u v h)
  let e := oppositeEquiv hG huv
  have hpoint (a : OtherNeighbors G u v) : w v (e a).1 ≤ w u a.1 := by
    have hab := adj_oppositeEquiv hG huv a
    have hsq := hclosed u v a.1 (e a).1 huv (e a).2.1 hab.symm a.2.1.symm
    rw [hskew a.1 (e a).1, hskew u a.1] at hsq
    have hbound := hmax (a.1, (e a).1) (Finset.mem_univ _)
    linarith only [hsq, hbound]
  have hsum : (∑ a : OtherNeighbors G u v, w v (e a).1) ≤ ∑ a : OtherNeighbors G u v, w u a.1 :=
    Finset.sum_le_sum fun a _ ↦ hpoint a
  rw [Fintype.sum_equiv e _ (fun b ↦ w v b.1) (fun _ ↦ rfl)] at hsum
  have hsu := sum_otherNeighbors w hsupport u v
  have hsv := sum_otherNeighbors w hsupport v u
  rw [hdiv u] at hsu
  rw [hdiv v, hskew u v] at hsv
  linarith only [hsum, hsu, hsv, hW]

/-- Subtracting the projection onto the masked gradients gives a skew edge label of zero
divergence. -/
private lemma exists_divergenceFree_sub_gradient {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → V → ℝ)
    (hw : ∀ u v, w v u = -w u v) (hw₀ : ∀ u v, ¬G.Adj u v → w u v = 0) :
    ∃ f : V → ℝ,
      let r (u v : V) := w u v - (if G.Adj u v then f v - f u else 0)
      (∀ u v, r v u = -r u v) ∧ (∀ u v, ¬G.Adj u v → r u v = 0) ∧ (∀ u, ∑ v, r u v = 0) := by
  classical
  let E := EuclideanSpace ℝ (V × V)
  let grad : (V → ℝ) →ₗ[ℝ] E :=
    { toFun := fun f => WithLp.toLp 2 fun p : V × V =>
        if G.Adj p.1 p.2 then f p.2 - f p.1 else 0
      map_add' := by
        intro f g
        ext p
        change (if G.Adj p.1 p.2 then (f p.2 + g p.2) - (f p.1 + g p.1) else 0) =
          (if G.Adj p.1 p.2 then f p.2 - f p.1 else 0) +
          (if G.Adj p.1 p.2 then g p.2 - g p.1 else 0)
        split_ifs <;> simp [add_sub_add_comm]
      map_smul' := by
        intro c f
        ext p
        change (if G.Adj p.1 p.2 then c * f p.2 - c * f p.1 else 0) =
          c * (if G.Adj p.1 p.2 then f p.2 - f p.1 else 0)
        split_ifs <;> simp [mul_sub] }
  let x : E := WithLp.toLp 2 fun p : V × V => w p.1 p.2
  let S : Submodule ℝ E := LinearMap.range grad
  obtain ⟨f, hf⟩ := LinearMap.mem_range.mp (S.starProjection_apply_mem x)
  have horth : x - grad f ∈ Sᗮ := by
    rw [hf]
    exact Submodule.sub_starProjection_mem_orthogonal x
  let r (i j : V) := w i j - (if G.Adj i j then f j - f i else 0)
  have hrskew (i j : V) : r j i = -r i j := by
    by_cases h : G.Adj i j
    · simp [r, h, h.symm, hw i j]
      abel
    · have h' : ¬G.Adj j i := fun hj => h hj.symm
      simp [r, h, h', hw i j]
  have hr₀ (i j : V) (h : ¬G.Adj i j) : r i j = 0 := by
    simp [r, h, hw₀ i j h]
  refine ⟨f, hrskew, hr₀, fun u ↦ ?_⟩
  -- Test orthogonality against the gradient of the indicator of `u`.
  let δ (i : V) : ℝ := if i = u then 1 else 0
  have hinner : inner ℝ (grad δ) (x - grad f) = 0 :=
    (S.mem_orthogonal _).mp horth _ (LinearMap.mem_range_self grad δ)
  have hpair (p : V × V) :
      inner ℝ (grad δ p) ((x - grad f) p) = (δ p.2 - δ p.1) * r p.1 p.2 := by
    rw [Real.inner_apply]
    change (if G.Adj p.1 p.2 then δ p.2 - δ p.1 else 0) * r p.1 p.2 = _
    by_cases h : G.Adj p.1 p.2
    · simp [h]
    · simp [h, hr₀ p.1 p.2 h]
  have hsum : (∑ i : V, ∑ j : V, (δ j - δ i) * r i j) = 0 := by
    change (∑ p : V × V, inner ℝ (grad δ p) ((x - grad f) p)) = 0 at hinner
    simpa only [hpair, Fintype.sum_prod_type] using hinner
  have hcol : (∑ i : V, ∑ j : V, δ j * r i j) = ∑ i : V, r i u := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [δ, ite_mul]
  have hrow : (∑ i : V, ∑ j : V, δ i * r i j) = ∑ j : V, r u j := by
    simp [δ, ite_mul]
  -- Skew-symmetry makes the incoming sum the negative of the outgoing sum.
  simp only [sub_mul, Finset.sum_sub_distrib, hcol, hrow, hrskew u,
    Finset.sum_neg_distrib] at hsum
  exact neg_eq_self.mp (sub_eq_zero.mp hsum)

/-- The forward step around the three colors has weight `1`, the backward step `-1`. -/
private def cyclicColorWeight (i j : Fin 3) : ℤ :=
  if i = j then 0 else if j = i + 1 then 1 else -1

private theorem cyclicColorWeight_skew :
    ∀ i j : Fin 3, cyclicColorWeight j i = -cyclicColorWeight i j := by
  decide

private theorem cyclicColorWeight_unit (i j : Fin 3) (h : i ≠ j) :
    cyclicColorWeight i j = 1 ∨ cyclicColorWeight i j = -1 := by
  simp only [cyclicColorWeight, ite_eq_right h]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Exhaust the color tuples with distinct colors at consecutive positions. -/
private theorem cyclicColorWeight_square :
    ∀ i j k l : Fin 3, i ≠ j → j ≠ k → k ≠ l → l ≠ i →
      cyclicColorWeight i j + cyclicColorWeight j k + cyclicColorWeight k l +
        cyclicColorWeight l i = 0 := by
  decide

private theorem exists_cyclic_color_label {V : Type*} (G : SimpleGraph V)
    (hG : G.Colorable 3) :
    ∃ w : V → V → ℝ,
      (∀ u v, w v u = -w u v) ∧
      (∀ u v, ¬ G.Adj u v → w u v = 0) ∧
      (∀ u v, G.Adj u v → w u v = 1 ∨ w u v = -1) ∧
      (∀ u v a b, G.Adj u v → G.Adj v b → G.Adj b a → G.Adj a u →
        w u v + w v b + w b a + w a u = 0) := by
  classical
  obtain ⟨c⟩ := hG
  let w : V → V → ℝ := fun u v =>
    if G.Adj u v then (cyclicColorWeight (c u) (c v) : ℝ) else 0
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro u v
    by_cases huv : G.Adj u v
    · simp only [w, ite_eq_left huv, ite_eq_left huv.symm,
        cyclicColorWeight_skew (c u) (c v), Int.cast_neg]
    · have hvu : ¬ G.Adj v u := fun h => huv h.symm
      simp [w, huv, hvu]
  · intro u v huv
    simp [w, huv]
  · intro u v huv
    rcases cyclicColorWeight_unit (c u) (c v) (c.valid huv) with h | h
    · exact Or.inl (by simp [w, huv, h])
    · exact Or.inr (by simp [w, huv, h])
  · intro u v a b huv hvb hba hau
    simpa only [w, ite_eq_left huv, ite_eq_left hvb, ite_eq_left hba, ite_eq_left hau,
      Int.cast_add, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ℝ))
        (cyclicColorWeight_square (c u) (c v) (c b) (c a)
          (c.valid huv) (c.valid hvb) (c.valid hba) (c.valid hau))

/-- Adjacent vertices have integer floors of opposite parity. -/
private theorem colorable_two_of_unit_edge_potential {V : Type*} (G : SimpleGraph V)
    (f : V → ℝ) (hf : ∀ u v, G.Adj u v → f v - f u = 1 ∨ f v - f u = -1) :
    G.Colorable 2 := by
  let p : V → Fin 2 := fun v => if ⌊f v⌋ % 2 = 0 then 0 else 1
  refine ⟨SimpleGraph.Coloring.mk p ?_⟩
  intro u v huv
  have hfloors : ⌊f v⌋ = ⌊f u⌋ + 1 ∨ ⌊f u⌋ = ⌊f v⌋ + 1 := by
    rcases hf u v huv with h | h
    · have hv : f v = f u + 1 := by
        simpa only [add_comm] using sub_eq_iff_eq_add.mp h
      exact Or.inl (by rw [hv, Int.floor_add_one])
    · have h' : f u - f v = 1 := by rw [← neg_sub, h, neg_neg]
      have hu : f u = f v + 1 := by
        simpa only [add_comm] using sub_eq_iff_eq_add.mp h'
      exact Or.inr (by rw [hu, Int.floor_add_one])
  change (if ⌊f u⌋ % 2 = 0 then (0 : Fin 2) else 1) ≠
    (if ⌊f v⌋ % 2 = 0 then (0 : Fin 2) else 1)
  split <;> split
  · exfalso; omega
  · decide
  · decide
  · exfalso; omega

-- The sign label is square-closed just by the colors. The square bijection also works
-- without a triangle-free hypothesis, so no separate orientation argument is needed.
private lemma colorable_two (hG : IsZeroTwo G) (hc : G.Colorable 3) : G.Colorable 2 := by
  classical
  obtain ⟨w, hskew, hsupport, hunit, hclosed⟩ := exists_cyclic_color_label G hc
  obtain ⟨f, hrskew, hrsupport, hdiv⟩ := exists_divergenceFree_sub_gradient G w hskew hsupport
  let r (u v : Fin n) := w u v - (if G.Adj u v then f v - f u else 0)
  have hrclosed (u v a b : Fin n) (huv : G.Adj u v) (hvb : G.Adj v b) (hba : G.Adj b a)
      (hau : G.Adj a u) : r u v + r v b + r b a + r a u = 0 := by
    simp only [r, ite_eq_left huv, ite_eq_left hvb, ite_eq_left hba, ite_eq_left hau]
    linarith only [hclosed u v a b huv hvb hba hau]
  have hr := eq_zero_of_squareClosed_of_divergenceFree hG r hrskew hrsupport hrclosed hdiv
  apply colorable_two_of_unit_edge_potential G f
  intro u v huv
  have h : w u v - (f v - f u) = 0 := by simpa only [r, ite_eq_left huv] using hr u v
  rw [← sub_eq_zero.mp h]
  exact hunit u v huv

/--
**No finite $(0,2)$-graph has chromatic number three.** For every natural number $n$ and
every simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ in which every two distinct vertices
have either zero or two common neighbors, the chromatic number of $G$ is not $3$. In particular,
the three-chromatic $(0,2)$-graph conjecture is false.

Williamson proves the stronger statement that every finite three-colourable $(0,2)$-graph is
bipartite (Theorem 2 of the source below).

Source: Christopher Williamson, Finite
Three-Colourable (0,2)-Graphs Are Bipartite, arXiv preprint (2026), arXiv:2607.10125,
https://arxiv.org/abs/2607.10125. Moved from
`OpenConjectures/Combinatorics/ThreeChromaticZeroTwoGraph`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  rintro ⟨n, G, hG, hchrom⟩
  have hc : G.Colorable 3 := SimpleGraph.chromaticNumber_le_iff_colorable.mp hchrom.le
  have htwo : G.chromaticNumber ≤ (2 : ℕ) := (colorable_two hG hc).chromaticNumber_le
  rw [hchrom] at htwo
  exact (by decide : ¬ (3 : ℕ∞) ≤ (2 : ℕ)) htwo

end MathlibExt.Combinatorics.ThreeChromaticZeroTwoGraphWanted
