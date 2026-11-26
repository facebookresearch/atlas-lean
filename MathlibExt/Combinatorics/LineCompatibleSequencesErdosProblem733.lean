/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# Counting complete line-size profiles of planar point sets

The complete line-size profile of a finite planar point set `P` records `|ℓ ∩ P|` once for every
line `ℓ` through two distinct points of `P`. The number of distinct complete profiles of `n`-point
sets is at most `exp(C √n)` for an absolute constant `C`. For `n = 0` the only profile is empty.

This formulation of Erdős Problem 733 uses all determined lines, as in Erdős Problem 607.
Distinct lines of equal size each contribute an entry, so three noncollinear points give
the profile `[2, 2, 2]`, one entry for each side of the triangle.

Source: T. F. Bloom, Erdős Problems, Problem #733, https://www.erdosproblems.com/733 (status
PROVED). UnsolvedMath record UM-30006999 (`EP-733`), dataset ulamai/UnsolvedMath v1.8.0.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LineCompatibleSequencesErdosProblem733Wanted

open Classical in
/-- **Line sizes of a planar point set.** For a finite set $P \subseteq \mathbb{R}^2$, this is
the multiset of the numbers $|\ell \cap P|$, where $\ell$ ranges over the lines determined by
$P$, that is, the distinct lines through two distinct points of $P$, each counted once. -/
noncomputable def lineSizes (P : Finset (ℝ × ℝ)) : Multiset ℕ :=
  ((P.offDiag.image fun pq => line[ℝ, pq.1, pq.2]).val.map fun ℓ =>
    (P.filter fun r => r ∈ ℓ).card)

/-- **Number of complete line-size profiles.** For a natural number $n$, $f(n)$ counts the
distinct multisets obtained from $n$-point sets $P \subseteq \mathbb{R}^2$. Each multiset
records $|\ell \cap P|$ once for every line $\ell$ through two distinct points of $P$. There are
finitely many such multisets, since each has at most $n^2$ entries, all at most $n$. -/
noncomputable def lineCompatibleCount (n : ℕ) : ℕ :=
  {X : Multiset ℕ | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ lineSizes P = X}.ncard

/-- **Subexponential count of complete line-size profiles (statement).** There is a real constant
$C$ such that for every natural number $n$, at most $e^{C \sqrt{n}}$ distinct complete line-size
profiles occur among $n$-point sets in the plane. In this formulation of Erdős Problem 733,
each profile records the number of points on every line determined by two distinct points of
the set. -/
def lineCompatibleCountSubexponential : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, (lineCompatibleCount n : ℝ) ≤ Real.exp (C * Real.sqrt n)

open Finset
open scoped BigOperators

-- A sweep from left to right gives a linear bound on the edges in a crossing-free drawing.

private noncomputable def edgeSlope {V : Type*} (x y : V → ℝ) (p q : V) : ℝ :=
  (y q - y p) / (x q - x p)

private noncomputable def edgeHeight {V : Type*} (x y : V → ℝ) (p q : V) (t : ℝ) : ℝ :=
  y p + edgeSlope x y p q * (t - x p)

private theorem edgeHeight_left {V : Type*} (x y : V → ℝ) (p q : V) :
    edgeHeight x y p q (x p) = y p := by simp [edgeHeight]

private theorem edgeHeight_right {V : Type*} (x y : V → ℝ) {p q : V}
    (h : x p < x q) : edgeHeight x y p q (x q) = y q := by
  unfold edgeHeight edgeSlope
  field_simp [ne_of_gt (sub_pos.mpr h)]
  ring

private theorem edgeHeight_lt_of_slope_lt {V : Type*} {x y : V → ℝ}
    {p a b : V} {t : ℝ} (ht : x p < t) (h : edgeSlope x y p a < edgeSlope x y p b) :
    edgeHeight x y p a t < edgeHeight x y p b t := by
  exact add_lt_add_right (mul_lt_mul_of_pos_right h (sub_pos.mpr ht)) _

private theorem slope_lt_of_edgeHeight_lt {V : Type*} {x y : V → ℝ}
    {p a b : V} {t : ℝ} (ht : x p < t)
    (h : edgeHeight x y p a t < edgeHeight x y p b t) :
    edgeSlope x y p a < edgeSlope x y p b := by
  simp only [edgeHeight, add_lt_add_iff_left] at h
  exact (mul_lt_mul_iff_left₀ (sub_pos.mpr ht)).1 h

/-- Each pair of consecutive outgoing edges is charged to the first vertex in its closed wedge.
The charge records whether the vertex is on the lower edge, on the upper edge, or between them. -/
private theorem card_edges_le_four_mul {V : Type*} [Fintype V]
    (x y : V → ℝ) (hx : Function.Injective x) (E : Finset (V × V))
    (forward : ∀ p q, (p, q) ∈ E → x p < x q)
    (noVertex : ∀ p q v, (p, q) ∈ E → x p < x v → x v < x q →
      edgeHeight x y p q (x v) ≠ y v)
    (noReverse : ∀ p q r s, (p, q) ∈ E → (r, s) ∈ E → ∀ a b : ℝ,
      x p ≤ a → x r ≤ a → a < b → b ≤ x q → b ≤ x s →
      edgeHeight x y p q b < edgeHeight x y r s b →
      edgeHeight x y p q a ≤ edgeHeight x y r s a) :
    E.card ≤ 4 * Fintype.card V := by
  classical
  let out (p : V) := univ.filter (fun q => (p, q) ∈ E)
  let slope (p q : V) := edgeSlope x y p q
  let height (p q : V) := edgeHeight x y p q
  have hslope (p : V) : Set.InjOn (slope p) (out p : Set V) := by
    intro a ha b hb hab
    by_contra hne
    have ha' := (mem_filter.mp (show a ∈ out p from ha)).2
    have hb' := (mem_filter.mp (show b ∈ out p from hb)).2
    have hheight (t : ℝ) : height p a t = height p b t := by
      change y p + slope p a * (t - x p) = y p + slope p b * (t - x p)
      rw [hab]
    rcases lt_or_gt_of_ne (fun h => hne (hx h)) with h | h
    · exact noVertex p b a hb' (forward p a ha') h
        ((hheight (x a)).symm.trans (edgeHeight_right x y (forward p a ha')))
    · exact noVertex p a b ha' (forward p b hb') h
        ((hheight (x b)).trans (edgeHeight_right x y (forward p b hb')))
  let degrees (p : V) := (out p).card
  let slopes (p : V) := (out p).image (slope p)
  have hslopes (p : V) : (slopes p).card = degrees p :=
    card_image_of_injOn (hslope p)
  have hexists (p : V) (i : Fin (degrees p)) :
      ∃ q, (p, q) ∈ E ∧ slope p q = (slopes p).orderEmbOfFin (hslopes p) i := by
    obtain ⟨q, hq, heq⟩ := mem_image.mp (orderEmbOfFin_mem (slopes p) (hslopes p) i)
    exact ⟨q, (mem_filter.mp (show q ∈ out p from hq)).2, heq⟩
  choose endpoints hends using hexists
  have hendmem (p : V) (i : Fin (degrees p)) := (hends p i).1
  have hendslope (p : V) (i : Fin (degrees p)) := (hends p i).2
  let wedges := Σ p, Fin (degrees p - 1)
  let lowIndex (w : wedges) : Fin (degrees w.1) := ⟨w.2, by omega⟩
  let highIndex (w : wedges) : Fin (degrees w.1) := ⟨w.2.val + 1, by omega⟩
  let lo (w : wedges) := endpoints w.1 (lowIndex w)
  let hi (w : wedges) := endpoints w.1 (highIndex w)
  have hlmem (w : wedges) := hendmem w.1 (lowIndex w)
  have hhmem (w : wedges) := hendmem w.1 (highIndex w)
  have hs (w : wedges) : slope w.1 (lo w) < slope w.1 (hi w) := by
    simp only [lo, hi, hendslope]
    exact ((slopes w.1).orderEmbOfFin _).strictMono (by
      change w.2.val < w.2.val + 1
      omega)
  have hgap (w : wedges) {t : ℝ} (ht : x w.1 < t) :
      height w.1 (lo w) t < height w.1 (hi w) t :=
    edgeHeight_lt_of_slope_lt ht (hs w)
  let inside (w : wedges) (v : V) :=
    x w.1 < x v ∧ x v ≤ x (lo w) ∧ x v ≤ x (hi w) ∧
      height w.1 (lo w) (x v) ≤ y v ∧ y v ≤ height w.1 (hi w) (x v)
  let candidates (w : wedges) := (univ.filter (inside w)).image x
  have hnonempty (w : wedges) : (candidates w).Nonempty := by
    have hl := forward w.1 (lo w) (hlmem w)
    have hh := forward w.1 (hi w) (hhmem w)
    rcases le_total (x (lo w)) (x (hi w)) with h | h
    · exact ⟨_, mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hl, le_rfl, h,
        (edgeHeight_right x y hl).le, (edgeHeight_right x y hl).symm.le.trans (hgap w hl).le⟩)⟩
    · exact ⟨_, mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hh, h, le_rfl,
        (hgap w hh).le.trans (edgeHeight_right x y hh).le, (edgeHeight_right x y hh).symm.le⟩)⟩
  have hex (w : wedges) : ∃ v, inside w v ∧ ∀ u, inside w u → x v ≤ x u := by
    obtain ⟨v, hv, he⟩ := mem_image.mp (min'_mem _ (hnonempty w))
    exact ⟨v, (mem_filter.mp hv).2, fun u hu => he.le.trans
      (min'_le _ _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hu⟩)))⟩
  choose dest hdest hmin using hex
  -- Comparing wedges at the same destination requires recording which side contains it.
  let kind (w : wedges) : Fin 3 :=
    if y (dest w) = height w.1 (lo w) (x (dest w)) then 0
    else if y (dest w) = height w.1 (hi w) (x (dest w)) then 1 else 2
  have hover {u v : wedges} (hd : dest u = dest v) (hk : kind u = kind v) :
      height u.1 (lo u) (x (dest u)) < height v.1 (hi v) (x (dest u)) := by
    obtain ⟨hu, -, -, hul, huh⟩ := hdest u
    obtain ⟨hv, -, -, hvl, hvh⟩ := hdest v
    by_contra! h
    rw [hd] at h hul huh hu
    have eq1 : y (dest u) = height u.1 (lo u) (x (dest u)) := by rw [hd]; linarith
    have eq2 : y (dest v) = height v.1 (hi v) (x (dest v)) := by linarith
    have ne2 : y (dest v) ≠ height v.1 (lo v) (x (dest v)) :=
      ne_of_gt ((hgap v hv).trans_le (le_of_eq eq2.symm))
    have hku : kind u = 0 := by dsimp [kind]; rw [ite_eq_left eq1]
    have hkv : kind v = 1 := by dsimp [kind]; rw [ite_eq_right ne2, ite_eq_left eq2]
    exact (by decide : (0 : Fin 3) ≠ 1) (hku.symm.trans (hk.trans hkv))
  have hiDest (u v : wedges) (hd : dest u = dest v) (hk : kind u = kind v)
      (hle : x u.1 ≤ x v.1) : x v.1 ≤ x u.1 := by
    by_contra! hlt
    obtain ⟨hu, hul, huh, -, -⟩ := hdest u
    obtain ⟨hv, hvl, hvh, -, -⟩ := hdest v
    rw [← hd] at hv hvl hvh
    have h₁ := noReverse u.1 (lo u) v.1 (hi v) (hlmem u) (hhmem v) _ _
      hle le_rfl hv hul hvh (hover hd hk)
    have ho := hover hd.symm hk.symm
    rw [← hd] at ho
    have h₂ := noReverse v.1 (lo v) u.1 (hi u) (hlmem v) (hhmem u) _ _
      le_rfl hle hv hvl huh ho
    simp only [edgeHeight_left] at h₁ h₂
    exact (not_le_of_gt hv) (hmin u v.1 ⟨hlt, hv.le.trans hul, hv.le.trans huh, h₁, h₂⟩)
  have hinj : Function.Injective (fun w : wedges => (dest w, kind w)) := by
    intro u v he
    obtain ⟨hd, hk⟩ := Prod.mk.inj he
    have ho := hover hd hk
    have ho' := hover hd.symm hk.symm
    have heq : u.1 = v.1 := hx (le_antisymm
      (by by_contra! h; exact (not_le_of_gt h) (hiDest v u hd.symm hk.symm h.le))
      (by by_contra! h; exact (not_le_of_gt h) (hiDest u v hd hk h.le)))
    obtain ⟨p, i⟩ := u
    obtain ⟨q, j⟩ := v
    change p = q at heq
    subst q
    congr 1
    apply Fin.ext
    have hfirst := slope_lt_of_edgeHeight_lt (hdest (⟨p, i⟩ : wedges)).1 ho
    have hsecond := slope_lt_of_edgeHeight_lt (hdest (⟨p, j⟩ : wedges)).1 ho'
    change slope p (lo (⟨p, i⟩ : wedges)) < slope p (hi (⟨p, j⟩ : wedges)) at hfirst
    change slope p (lo (⟨p, j⟩ : wedges)) < slope p (hi (⟨p, i⟩ : wedges)) at hsecond
    simp only [lo, hi, hendslope,
      OrderEmbedding.lt_iff_lt] at hfirst hsecond
    change i.val < j.val + 1 at hfirst
    change j.val < i.val + 1 at hsecond
    omega
  have hw := Fintype.card_le_of_injective _ hinj
  simp only [wedges, Fintype.card_sigma, Fintype.card_fin, Fintype.card_prod] at hw
  have hE : E.card = ∑ p : V, degrees p := by
    have h := card_eq_sum_card_fiberwise (s := E) (t := (univ : Finset V))
      (f := Prod.fst) (by simp)
    rw [h]
    apply sum_congr rfl
    intro p _
    symm
    exact card_bij (fun q _ => (p, q))
      (by simp [out]) (by simp) (by simp [out]; aesop)
  rw [hE]
  calc
    _ ≤ ∑ p : V, (degrees p - 1 + 1) :=
      sum_le_sum (fun p _ => by omega)
    _ = (∑ p : V, (degrees p - 1)) + Fintype.card V := by simp [sum_add_distrib]
    _ ≤ _ := by omega

private def edgeVertices {V : Type*} [DecidableEq V] (e : V × V) : Finset V :=
  {e.1, e.2}

private def crosses {V : Type*} (x y : V → ℝ) (e f : V × V) : Prop :=
  edgeSlope x y e.1 e.2 ≠ edgeSlope x y f.1 f.2 ∧
    ∃ t, x e.1 < t ∧ t < x e.2 ∧ x f.1 < t ∧ t < x f.2 ∧
      edgeHeight x y e.1 e.2 t = edgeHeight x y f.1 f.2 t

private theorem crossing_abscissa_unique {V : Type*} {x y : V → ℝ} {e f : V × V}
    (hs : edgeSlope x y e.1 e.2 ≠ edgeSlope x y f.1 f.2) {a b : ℝ}
    (ha : edgeHeight x y e.1 e.2 a = edgeHeight x y f.1 f.2 a)
    (hb : edgeHeight x y e.1 e.2 b = edgeHeight x y f.1 f.2 b) : a = b := by
  unfold edgeHeight at ha hb
  have h : (edgeSlope x y e.1 e.2 - edgeSlope x y f.1 f.2) * (a - b) = 0 := by
    nlinarith only [ha, hb]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hs))

private theorem crossing_vertices_card {V : Type*} [DecidableEq V] {x y : V → ℝ}
    {e f : V × V} (h : crosses x y e f) :
    ((edgeVertices e) ∪ edgeVertices f).card = 4 := by
  obtain ⟨hs, t, he₁, he₂, hf₁, hf₂, ht⟩ := h
  have he : e.1 ≠ e.2 := fun he => (he₁.trans he₂).ne (congrArg x he)
  have hf : f.1 ≠ f.2 := fun hf => (hf₁.trans hf₂).ne (congrArg x hf)
  have hdiff : Disjoint (edgeVertices e) (edgeVertices f) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    have hheight (g : V × V) (hg : x g.1 < x g.2) (hv : v ∈ edgeVertices g) :
        edgeHeight x y g.1 g.2 (x v) = y v := by
      rcases (show v = g.1 ∨ v = g.2 by simpa [edgeVertices] using hv) with hvg | hvg
      · rw [hvg, edgeHeight_left]
      · rw [hvg, edgeHeight_right x y hg]
    have hvx := crossing_abscissa_unique hs ht
      ((hheight e (he₁.trans he₂) hv).trans (hheight f (hf₁.trans hf₂) hw).symm)
    rcases (show v = e.1 ∨ v = e.2 by simpa [edgeVertices] using hv) with hve | hve
    · exact he₁.ne (hvx.trans (congrArg x hve)).symm
    · exact he₂.ne (hvx.trans (congrArg x hve))
  rw [card_union_of_disjoint hdiff]
  simp [edgeVertices, card_pair_eq_two_iff.mpr he, card_pair_eq_two_iff.mpr hf]

private theorem crosses_of_reverse {V : Type*} {x y : V → ℝ} {e f : V × V} {a b : ℝ}
    (hea : x e.1 ≤ a) (hfa : x f.1 ≤ a) (hab : a < b)
    (heb : b ≤ x e.2) (hfb : b ≤ x f.2)
    (ha : edgeHeight x y f.1 f.2 a < edgeHeight x y e.1 e.2 a)
    (hb : edgeHeight x y e.1 e.2 b < edgeHeight x y f.1 f.2 b) :
    crosses x y e f := by
  have hs : edgeSlope x y e.1 e.2 ≠ edgeSlope x y f.1 f.2 := by
    intro hs
    unfold edgeHeight at ha hb
    rw [hs] at ha hb
    linarith
  let g t := edgeHeight x y f.1 f.2 t - edgeHeight x y e.1 e.2 t
  have hga : g a < 0 := sub_neg.mpr ha
  have hgb : 0 < g b := sub_pos.mpr hb
  have hcont : Continuous g := by unfold g edgeHeight; fun_prop
  obtain ⟨t, ht, hzero⟩ :=
    intermediate_value_Icc hab.le hcont.continuousOn (show 0 ∈ Set.Icc (g a) (g b) from
      ⟨hga.le, hgb.le⟩)
  have hlt : a < t := lt_of_le_of_ne ht.1 (by rintro rfl; exact hga.ne hzero)
  have hgt : t < b := lt_of_le_of_ne ht.2 (by rintro rfl; exact hgb.ne' hzero)
  exact ⟨hs, t, hea.trans_lt hlt, hgt.trans_le heb, hfa.trans_lt hlt, hgt.trans_le hfb,
    (sub_eq_zero.mp hzero).symm⟩

open Classical in
private theorem count_sampled_edges {V : Type*} [DecidableEq V]
    (x y : V → ℝ) (hx : Function.Injective x) (E : Finset (V × V))
    (forward : ∀ e ∈ E, x e.1 < x e.2)
    (noVertex : ∀ e ∈ E, ∀ v, x e.1 < x v → x v < x e.2 →
      edgeHeight x y e.1 e.2 (x v) ≠ y v)
    (P : Finset V) :
    (E.filter fun e => edgeVertices e ⊆ P).card ≤
      4 * P.card + ((E ×ˢ E).filter fun (ef : (V × V) × (V × V)) =>
        crosses x y ef.1 ef.2 ∧ edgeVertices ef.1 ∪ edgeVertices ef.2 ⊆ P).card := by
  classical
  let C := (E ×ˢ E).filter fun ef =>
    crosses x y ef.1 ef.2 ∧ edgeVertices ef.1 ∪ edgeVertices ef.2 ⊆ P
  let S := E.filter fun e => edgeVertices e ⊆ P
  -- Delete one edge from every crossing pair in the sampled drawing.
  let T := S \ C.image Prod.fst
  have hT : T.card ≤ 4 * P.card := by
    let f : P × P ↪ V × V := ⟨fun e => (e.1.val, e.2.val), by
      intro a b h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))⟩
    let U := T.preimage f f.injective.injOn
    have hU : U.map f = T := by
      ext e
      rw [mem_map]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact mem_preimage.mp (show u ∈ T.preimage (f : P × P → V × V) _ from hu)
      · intro he
        have h : edgeVertices e ⊆ P := (mem_filter.mp (mem_sdiff.mp he).1).2
        let u : P × P := (⟨e.1, h (by simp [edgeVertices])⟩, ⟨e.2, h (by simp [edgeVertices])⟩)
        exact ⟨u, mem_preimage.mpr (show f u ∈ T from he), rfl⟩
    have hmem (p q : P) (h : (p, q) ∈ U) : (p.val, q.val) ∈ T := by
      change (p, q) ∈ T.preimage (f : P × P → V × V) _ at h
      rw [mem_preimage] at h
      exact h
    have hE {e} (h : e ∈ T) : e ∈ E := (mem_filter.mp (mem_sdiff.mp h).1).1
    have hc {e f} (he : e ∈ T) (hf : f ∈ T) : ¬ crosses x y e f := by
      intro hcross
      exact (mem_sdiff.mp he).2 (mem_image.mpr ⟨(e, f), mem_filter.mpr
        ⟨mem_product.mpr ⟨hE he, hE hf⟩, hcross,
          union_subset (mem_filter.mp (mem_sdiff.mp he).1).2
            (mem_filter.mp (mem_sdiff.mp hf).1).2⟩, rfl⟩)
    have h := card_edges_le_four_mul (x ∘ Subtype.val) (y ∘ Subtype.val)
      (hx.comp Subtype.val_injective) U
      (fun p q h => forward _ (hE (hmem p q h)))
      (fun p q v h => noVertex _ (hE (hmem p q h)) v)
      (by
        intro p q r s hpq hrs a b ha hr hab hq hs hb
        by_contra! ha'
        exact hc (hmem p q hpq) (hmem r s hrs)
          (crosses_of_reverse ha hr hab hq hs ha' hb))
    rw [← hU, card_map]
    simpa using h
  exact (card_le_card_sdiff_add_card (s := S) (t := C.image Prod.fst)).trans
    (Nat.add_le_add hT card_image_le)



-- Independent vertex sampling turns the linear edge bound into a cubic crossing bound.

private noncomputable def sampleWeight {V : Type*} [Fintype V]
    (p : ℝ) (s : V → Bool) : ℝ :=
  ∏ v : V, if s v then p else 1 - p

private theorem sum_sampleWeight_choose {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (U : Finset V) :
    ∑ s : V → Bool, (if ∀ v ∈ U, s v = true then sampleWeight p s else 0) = p ^ U.card := by
  classical
  let f (v : V) (b : Bool) := if b then p else if v ∈ U then 0 else 1 - p
  have h (s : V → Bool) :
      (if ∀ v ∈ U, s v = true then sampleWeight p s else 0) = ∏ v : V, f v (s v) := by
    split_ifs with hs
    · apply prod_congr rfl
      intro v _
      by_cases hv : v ∈ U
      · simp [f, hs v hv]
      · simp [f, hv]
    · push Not at hs
      obtain ⟨v, hv, hs⟩ := hs
      have hs' : s v = false := by cases h : s v <;> simp_all
      symm
      exact prod_eq_zero (mem_univ v) (by simp [f, hs', hv])
  simp_rw [h]
  rw [← Fintype.prod_sum]
  have hsum (v : V) : ∑ b : Bool, f v b = if v ∈ U then p else 1 := by
    by_cases hv : v ∈ U <;> simp [f, hv]
  simp_rw [hsum]
  rw [prod_ite, prod_const, prod_const, one_pow, mul_one]
  simp

private def sampleVertices {V : Type*} [Fintype V] (s : V → Bool) : Finset V :=
  univ.filter (fun v => s v = true)

private theorem sum_sampleWeight_select {V D : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (T : Finset D) (vertices : D → Finset V) (a : ℕ)
    (ha : ∀ d ∈ T, (vertices d).card = a) :
    (∑ s : V → Bool, sampleWeight p s *
      ((T.filter fun d => vertices d ⊆ sampleVertices s).card : ℝ)) = p ^ a * T.card := by
  classical
  have h (s : V → Bool) (U : Finset V) :
      U ⊆ sampleVertices s ↔ ∀ v ∈ U, s v = true := by simp [sampleVertices, Finset.subset_iff]
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter, mul_sum]
  conv_lhs => rw [sum_comm]
  calc
    _ = ∑ d ∈ T, p ^ (vertices d).card := by
      apply sum_congr rfl
      intro d _
      simpa only [h, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
        using sum_sampleWeight_choose p (vertices d)
    _ = _ := by
      calc
        _ = ∑ _d ∈ T, p ^ a := sum_congr rfl (fun d hd => by rw [ha d hd])
        _ = _ := by simp [mul_comm]

private theorem sampling_inequality {V A B : Type*} [Fintype V] [DecidableEq V]
    (E : Finset A) (C : Finset B) (ends : A → Finset V) (crossEnds : B → Finset V)
    (hE : ∀ e ∈ E, (ends e).card = 2) (hC : ∀ c ∈ C, (crossEnds c).card = 4)
    (hbound : ∀ P : Finset V, (E.filter fun e => ends e ⊆ P).card ≤
      4 * P.card + (C.filter fun c => crossEnds c ⊆ P).card)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    p ^ 2 * E.card ≤ 4 * p * Fintype.card V + p ^ 4 * C.card := by
  classical
  have hnonneg (s : V → Bool) : 0 ≤ sampleWeight p s := by
    apply prod_nonneg
    intro v _
    split <;> linarith [hp.1, hp.2]
  have hvert : ∑ s : V → Bool, (sampleWeight p s * (sampleVertices s).card) =
      p * Fintype.card V := by
    have hfilter (s : V → Bool) :
        (univ.filter fun (v : V) => ({v} : Finset V) ⊆ sampleVertices s) = sampleVertices s := by
      ext v
      simp only [mem_filter, mem_univ, true_and, singleton_subset_iff]
    have hc := sum_sampleWeight_select p (D := V) univ (fun v => ({v} : Finset V)) 1
      (fun v _ => card_singleton v)
    simp only [hfilter, pow_one, card_univ] at hc
    exact hc
  have hmul (s : V → Bool) :
      sampleWeight p s * (E.filter (fun e => ends e ⊆ sampleVertices s)).card ≤
        4 * (sampleWeight p s * (sampleVertices s).card) +
          sampleWeight p s * (C.filter (fun c => crossEnds c ⊆ sampleVertices s)).card := by
    have hcast : ((E.filter fun e => ends e ⊆ sampleVertices s).card : ℝ) ≤
        4 * (sampleVertices s).card + (C.filter fun c => crossEnds c ⊆ sampleVertices s).card := by
      exact_mod_cast hbound (sampleVertices s)
    nlinarith only [mul_le_mul_of_nonneg_left hcast (hnonneg s)]
  simpa only [sum_add_distrib, ← mul_sum, sum_sampleWeight_select p E ends 2 hE,
    sum_sampleWeight_select p C crossEnds 4 hC, hvert, mul_assoc]
    using sum_le_sum (s := (univ : Finset (V → Bool))) (fun s _ => hmul s)

private theorem rich_bound_of_sampling (n m e c k : ℝ)
    (hn : 0 < n) (hm : 0 ≤ m) (hk : 0 < k)
    (he : k * m / 2 ≤ e) (hc : c ≤ m ^ 2)
    (hsample : ∀ p ∈ Set.Icc (0 : ℝ) 1, p ^ 2 * e ≤ 4 * p * n + p ^ 4 * c) :
    m ≤ 1024 * (n ^ 2 / k ^ 3 + n / k) := by
  by_cases hsmall : e ≤ 8 * n
  · have hnk : n / k ≤ n ^ 2 / k ^ 3 + n / k := by linarith [show 0 ≤ n^2 / k^3 by positivity]
    have hkm : m ≤ 16 * (n / k) := by
      rw [← mul_div_assoc, le_div_iff₀ hk]
      linarith
    linarith
  · have he' : 0 < e := by linarith
    have hp : 8 * n / e ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one he').mpr (le_of_lt (lt_of_not_ge hsmall))⟩
    have h := hsample (8 * n / e) hp
    have he0 : e ≠ 0 := he'.ne'
    have hcube : e ^ 3 ≤ 128 * n ^ 2 * c := by
      have hclear : (8*n)^2 * e^3 ≤ 4*(8*n)*n*e^3 + (8*n)^4*c := by
        have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ e^4 by positivity)
        convert hh using 1 <;> field_simp
      apply (mul_le_mul_iff_right₀ (show 0 < 32 * n^2 by positivity)).mp
      nlinarith only [hclear]
    have hkm : (k * m / 2)^3 ≤ 128 * n^2 * m^2 :=
      (pow_le_pow_left₀ (by positivity) he _).trans
        (hcube.trans (mul_le_mul_of_nonneg_left hc (by positivity)))
    by_cases hm0 : m = 0
    · subst m
      positivity
    have hpow : 0 < m ^ 2 := sq_pos_of_pos (lt_of_le_of_ne hm (Ne.symm hm0))
    have hk3 : 0 < k ^ 3 := by positivity
    calc
      m ≤ 1024 * n^2 / k^3 := by
        apply (le_div_iff₀ hk3).mpr
        apply le_of_mul_le_mul_left _ hpow
        nlinarith only [hkm]
      _ ≤ _ := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [show 0 ≤ n/k by positivity]

-- Joining consecutive points on each line realizes the graph to which sampling is applied.

private theorem exists_injective_projection (P : Finset (ℝ × ℝ)) :
    ∃ a : ℝ, Set.InjOn (fun p : ℝ × ℝ => p.1 + a * p.2) (P : Set (ℝ × ℝ)) := by
  classical
  let bad := P.offDiag.image (fun pq => (pq.2.1 - pq.1.1) / (pq.1.2 - pq.2.2))
  obtain ⟨a, ha⟩ := bad.finite_toSet.exists_notMem
  refine ⟨a, ?_⟩
  intro p hp q hq h
  change p.1 + a*p.2 = q.1 + a*q.2 at h
  by_contra hne
  by_cases hy : p.2 = q.2
  · exact hne (Prod.ext (by rw [hy] at h; linarith) hy)
  · apply ha
    exact mem_image.mpr ⟨(p, q), mem_offDiag.mpr ⟨hp, hq, hne⟩,
      (div_eq_iff (sub_ne_zero.mpr hy)).2 (by nlinarith)⟩

private theorem mem_line_iff_height (a : ℝ) {p q r : ℝ × ℝ}
    (h : p.1 + a * p.2 < q.1 + a * q.2) :
    r ∈ line[ℝ, p, q] ↔
      edgeHeight (fun r : ℝ × ℝ => r.1 + a * r.2) Prod.snd p q (r.1 + a * r.2) = r.2 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  let x (r : ℝ × ℝ) := r.1 + a * r.2
  let t := (x r - x p) / (x q - x p)
  have ht : t * (x q - x p) = x r - x p := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr h))
  have hH : edgeHeight x Prod.snd p q (x r) = p.2 + t * (q.2 - p.2) := by
    dsimp [edgeHeight, edgeSlope, t]
    ring
  change (∃ s : ℝ, AffineMap.lineMap p q s = r) ↔ edgeHeight x Prod.snd p q (x r) = r.2
  rw [hH]
  constructor
  · rintro ⟨s, hs⟩
    have hfirst : s * (q.1 - p.1) + p.1 = r.1 := congrArg Prod.fst hs
    have hsecond : s * (q.2 - p.2) + p.2 = r.2 := congrArg Prod.snd hs
    have hmul : s * (x q - x p) = x r - x p := by
      dsimp [x]
      linear_combination hfirst + a * hsecond
    have hst : s = t := mul_right_cancel₀ (ne_of_gt (sub_pos.mpr h)) (hmul.trans ht.symm)
    rw [← hst]
    linarith
  · intro h₂
    use t
    apply Prod.ext
    · change t * (q.1 - p.1) + p.1 = r.1
      dsimp [x] at ht
      linear_combination (norm := ring_nf) ht - a * h₂
    · change t * (q.2 - p.2) + p.2 = r.2
      linarith

open Classical in
private theorem rich_affine_graphs {V : Type*} [Fintype V]
    (x y : V → ℝ) (hx : Function.Injective x) (L : Finset (ℝ × ℝ))
    (k : ℕ) (hk : 2 ≤ k) (hn : 0 < Fintype.card V)
    (hrich : ∀ l ∈ L, k ≤ ((univ : Finset V).filter (fun p => y p = l.1 * x p + l.2)).card) :
    (L.card : ℝ) ≤ 1024 *
      ((Fintype.card V : ℝ) ^ 2 / (k : ℝ) ^ 3 + (Fintype.card V : ℝ) / (k : ℝ)) := by
  classical
  let points (l : L) := (univ : Finset V).filter (fun p => y p = l.val.1 * x p + l.val.2)
  let xs (l : L) := (points l).image x
  have hcard (l : L) : (xs l).card = (points l).card :=
    card_image_of_injective _ hx
  let ord (l : L) := (xs l).orderEmbOfFin rfl
  have hex (l : L) (i : Fin (xs l).card) :
      ∃ p, y p = l.val.1 * x p + l.val.2 ∧ x p = ord l i := by
    obtain ⟨p, hp, he⟩ := mem_image.mp (orderEmbOfFin_mem (xs l) rfl i)
    exact ⟨p, (mem_filter.mp hp).2, he⟩
  choose pt hpt using hex
  let Edges := Σ l : L, Fin ((xs l).card - 1)
  let leftI (e : Edges) : Fin (xs e.1).card := ⟨e.2, by omega⟩
  let rightI (e : Edges) : Fin (xs e.1).card := ⟨e.2.val + 1, by omega⟩
  let toPair (e : Edges) := (pt e.1 (leftI e), pt e.1 (rightI e))
  have hforward (e : Edges) : x (toPair e).1 < x (toPair e).2 := by
    simp only [toPair, (hpt _ _).2]
    exact (ord e.1).strictMono (by change e.2.val < e.2.val + 1; omega)
  have hSlope (e : Edges) : edgeSlope x y (toPair e).1 (toPair e).2 = e.1.val.1 := by
    have ha := (hpt e.1 (leftI e)).1
    have hb := (hpt e.1 (rightI e)).1
    change y (toPair e).1 = _ at ha
    change y (toPair e).2 = _ at hb
    unfold edgeSlope
    rw [ha, hb, div_eq_iff (ne_of_gt (sub_pos.mpr (hforward e)))]
    ring
  have hHeight (e : Edges) (t : ℝ) :
      edgeHeight x y (toPair e).1 (toPair e).2 t = e.1.val.1 * t + e.1.val.2 := by
    have h := (hpt e.1 (leftI e)).1
    change y (toPair e).1 = _ at h
    rw [edgeHeight, hSlope, h]
    ring
  have hindex (e f : Edges) (hef : e.1 = f.1) {t : ℝ}
      (he1 : x (toPair e).1 ≤ t) (he2 : t < x (toPair e).2)
      (hf1 : x (toPair f).1 ≤ t) (hf2 : t < x (toPair f).2) : e = f := by
    obtain ⟨l, i⟩ := e
    obtain ⟨m, j⟩ := f
    change l = m at hef
    subst m
    have h1 := hf1.trans_lt he2
    have h2 := he1.trans_lt hf2
    simp only [toPair, (hpt _ _).2, OrderEmbedding.lt_iff_lt] at h1 h2
    change j.val < i.val + 1 at h1
    change i.val < j.val + 1 at h2
    congr 1
    exact Fin.ext (by omega)
  have hinj : Function.Injective toPair := by
    intro e f h
    have hs : e.1.val.1 = f.1.val.1 := by rw [← hSlope e, ← hSlope f, h]
    have hi : e.1.val.2 = f.1.val.2 := by
      have hh := (hHeight e 0).symm.trans (h ▸ hHeight f 0)
      simpa using hh
    apply hindex e f (Subtype.ext (Prod.ext hs hi))
      (t := x (toPair e).1) le_rfl (hforward e)
    · rw [h]
    · rw [← h]; exact hforward e
  let E := (univ : Finset Edges).image toPair
  have hnoVertex (e : Edges) (v : V) (h1 : x (toPair e).1 < x v) (h2 : x v < x (toPair e).2) :
      edgeHeight x y (toPair e).1 (toPair e).2 (x v) ≠ y v := by
    intro hv
    rw [hHeight] at hv
    have hm : x v ∈ xs e.1 := mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hv.symm⟩)
    have hm' : x v ∈ Set.range (ord e.1) := by
      change x v ∈ Set.range ((xs e.1).orderEmbOfFin rfl)
      rwa [range_orderEmbOfFin]
    obtain ⟨i, hxi⟩ := hm'
    simp only [toPair, (hpt _ _).2, ← hxi, OrderEmbedding.lt_iff_lt] at h1 h2
    change (e.2 : ℕ) < i.val at h1
    change i.val < e.2.val + 1 at h2
    omega
  have heach (e : V × V) (he : e ∈ E) : ∃ a : Edges, toPair a = e := by
    obtain ⟨a, -, ha⟩ := mem_image.mp he
    exact ⟨a, ha⟩
  let C := (E ×ˢ E).filter fun ef => crosses x y ef.1 ef.2
  have hc : C.card ≤ L.card ^ 2 := by
    let own (e : V × V) := (edgeSlope x y e.1 e.2, edgeHeight x y e.1 e.2 0)
    have ho (e : Edges) : own (toPair e) = e.1.val := by
      apply Prod.ext (hSlope e)
      simpa only [own, mul_zero, zero_add] using hHeight e 0
    rw [sq, ← card_product]
    apply card_le_card_of_injOn (fun ef : (V × V) × (V × V) => (own ef.1, own ef.2))
    · rintro ⟨p, q⟩ hef
      have hm := (mem_product.mp (mem_filter.mp (show (p, q) ∈ C from hef)).1)
      obtain ⟨e, rfl⟩ := heach p hm.1
      obtain ⟨f, rfl⟩ := heach q hm.2
      exact mem_product.mpr ⟨(show own (toPair e) ∈ L by rw [ho]; exact e.1.2),
        (show own (toPair f) ∈ L by rw [ho]; exact f.1.2)⟩
    · rintro ⟨p, q⟩ h₁ ⟨r, s⟩ h₂ h
      have hm₁ := mem_filter.mp (show (p, q) ∈ C from h₁)
      have hm₂ := mem_filter.mp (show (r, s) ∈ C from h₂)
      obtain ⟨e, rfl⟩ := heach p (mem_product.mp hm₁.1).1
      obtain ⟨f, rfl⟩ := heach q (mem_product.mp hm₁.1).2
      obtain ⟨g, rfl⟩ := heach r (mem_product.mp hm₂.1).1
      obtain ⟨j, rfl⟩ := heach s (mem_product.mp hm₂.1).2
      obtain ⟨hle, hlf⟩ := Prod.mk.inj h
      simp only [ho] at hle hlf
      have he := Subtype.ext hle
      have hf := Subtype.ext hlf
      obtain ⟨hne, t, he1, he2, hf1, hf2, ht⟩ := hm₁.2
      obtain ⟨-, u, hg1, hg2, hj1, hj2, hu⟩ := hm₂.2
      rw [hHeight g, hHeight j, ← he, ← hf, ← hHeight e, ← hHeight f] at hu
      have htu := crossing_abscissa_unique hne ht hu
      subst u
      rw [hindex e g he he1.le he2 hg1.le hg2, hindex f j hf hf1.le hf2 hj1.le hj2]
  apply rich_bound_of_sampling (n := Fintype.card V) (e := E.card) (c := C.card)
  · exact_mod_cast hn
  · positivity
  · exact_mod_cast (show 0 < k by omega)
  · have hecards : E.card = ∑ l : L, ((xs l).card - 1) := by
      simp only [E, card_image_of_injective _ hinj, card_univ, Edges, Fintype.card_sigma,
        Fintype.card_fin]
    have he : k * L.card ≤ 2 * E.card := by
      rw [hecards, mul_sum]
      have hsum : (∑ _l : L, k) = k * L.card := by simp [mul_comm]
      rw [← hsum]
      apply sum_le_sum
      intro l _
      have h : k ≤ (xs l).card := by rw [hcard]; exact hrich l.val l.2
      omega
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (mul_comm 2 E.card ▸ he)
  · exact_mod_cast hc
  · intro p hp
    apply sampling_inequality E C edgeVertices
      (fun ef => edgeVertices ef.1 ∪ edgeVertices ef.2) _ _ _ p hp
    · intro e he
      obtain ⟨a, rfl⟩ := heach e he
      exact card_pair_eq_two_iff.mpr (fun h => (hforward a).ne (congrArg x h))
    · intro ef hef
      exact crossing_vertices_card (mem_filter.mp hef).2
    · intro P
      simpa only [C, filter_filter] using count_sampled_edges x y hx E
        (fun e he => by obtain ⟨a, rfl⟩ := heach e he; exact hforward a)
        (fun e he => by obtain ⟨a, rfl⟩ := heach e he; exact hnoVertex a) P



-- Logarithmic weights turn a bound on the number of rich lines into a count of multisets.

private noncomputable def cost (s : ℝ) (i : ℕ) : ℝ :=
  Real.log (1 + (i : ℝ) ^ 4 / s ^ 4)

private theorem sum_inverse_steps (s : ℕ) (hs : 0 < s) (n : ℕ) :
    ∑ i ∈ range n, (s : ℝ)^2 / (((s + i : ℕ) : ℝ) * ((s + i + 1 : ℕ) : ℝ)) ≤ s := by
  have he (i : ℕ) :
      (s : ℝ)^2 / (((s + i : ℕ) : ℝ) * ((s + i + 1 : ℕ) : ℝ)) =
        (s : ℝ)^2 / ((s + i : ℕ) : ℝ) - (s : ℝ)^2 / ((s + (i + 1) : ℕ) : ℝ) := by
    push_cast
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    field_simp
    ring
  simp_rw [he]
  rw [sum_range_sub', add_zero, pow_two, mul_div_cancel_right₀ _ (by exact_mod_cast hs.ne')]
  exact sub_le_self _ (by positivity)

private theorem cost_step_low (s : ℝ) (hs : 0 < s) (t : ℕ) :
    cost s (t + 1) - cost s t ≤ 4 * (t + 1 : ℝ)^3 / s^4 := by
  let a := (t : ℝ)
  let b := a + 1
  let A := 1 + a^4 / s^4
  let B := 1 + b^4 / s^4
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hA' : 1 ≤ A := le_add_of_nonneg_right (by positivity)
  have hAB : A ≤ B := by dsimp [A, B, b, a]; gcongr; linarith
  have hp : b^4 - a^4 ≤ 4 * b^3 := by
    dsimp [b, a]
    nlinarith only [sq_nonneg (t : ℝ), Nat.cast_nonneg (α := ℝ) t]
  simp only [cost, Nat.cast_add, Nat.cast_one]
  change Real.log B - Real.log A ≤ 4 * b^3 / s^4
  rw [← Real.log_div hB.ne' hA.ne']
  calc
    _ ≤ B/A - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = (B-A)/A := by field_simp
    _ ≤ B-A := (div_le_self (sub_nonneg.mpr hAB) hA')
    _ = (b^4 - a^4)/s^4 := by dsimp [A, B]; ring
    _ ≤ _ := by gcongr

private theorem cost_step_high (s : ℝ) (hs : 0 < s) (t : ℕ) (ht : 0 < t) :
    cost s (t+1) - cost s t ≤ 4 / (t : ℝ) := by
  let a := (t : ℝ)
  let b := a + 1
  let A := 1 + a^4 / s^4
  let B := 1 + b^4 / s^4
  have ha : 0 < a := by dsimp [a]; exact_mod_cast ht
  have hb : 0 < b := by dsimp [b]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have h₁ : 1 ≤ (b/a)^4 := by
    exact one_le_pow₀ ((le_div_iff₀ ha).2 (by dsimp [b]; linarith))
  have h₂ : (b/a)^4 * (a^4 / s^4) = b^4 / s^4 := by
    field_simp
  simp only [cost, Nat.cast_add, Nat.cast_one]
  change Real.log B - Real.log A ≤ 4 / a
  rw [← Real.log_div hB.ne' hA.ne']
  calc
    _ ≤ Real.log ((b/a)^4) := by
      apply Real.log_le_log (by positivity)
      apply (div_le_iff₀ hA).2
      dsimp [B, A]
      rw [mul_add, mul_one, h₂]
      linarith
    _ = 4 * Real.log (b/a) := by rw [Real.log_pow]; norm_num
    _ ≤ 4 * (b/a - 1) := by gcongr; exact Real.log_le_sub_one_of_pos (by positivity)
    _ = _ := by dsimp [b]; field_simp; ring

private theorem cost_sum_le {s n : ℕ} (hs : 0 < s) (A : ℝ) (hA : 0 ≤ A)
    (X : Multiset ℕ) (hX : ∀ i ∈ X, 1 ≤ i ∧ i ≤ s + n)
    (htail : ∀ i : ℕ, 1 ≤ i →
      ((X.filter (i ≤ ·)).card : ℝ) ≤ A * ((s : ℝ)^4 / (i : ℝ)^3 + (s : ℝ)^2 / i)) :
    (X.map (cost s)).sum ≤ 16 * A * s := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  let d (t : ℕ) := cost s (t + 1) - cost s t
  let tail (t : ℕ) : ℝ := (X.filter (t + 1 ≤ ·)).card
  have hid : (X.map (cost s)).sum = ∑ t ∈ range (s + n), tail t * d t := by
    have htelescope (i : ℕ) (hi : i ≤ s + n) :
        cost s i = ∑ t ∈ range (s + n), (if t + 1 ≤ i then d t else 0) := by
      rw [← sum_filter]
      have heq : (range (s + n)).filter (fun t => t + 1 ≤ i) = range i := by
        ext x
        simp
        omega
      rw [heq]
      dsimp [d]
      rw [sum_range_sub]
      simp [cost]
    dsimp [tail]
    clear tail htail
    induction X using Multiset.induction_on with
    | empty => simp
    | @cons a l ih =>
      have ha := (hX a (Multiset.mem_cons_self ..)).2
      rw [Multiset.map_cons, Multiset.sum_cons, ih (fun i hi => hX i (Multiset.mem_cons_of_mem hi)),
        htelescope a ha, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      by_cases hi : i < a <;> simp [hi, add_mul, add_comm]
  have hlow (t : ℕ) (ht : t < s) : tail t * d t ≤ 8 * A := by
    let a : ℝ := t + 1
    have ha : 0 < a := by dsimp [a]; positivity
    have ha' : a ≤ s := by dsimp [a]; exact_mod_cast Nat.succ_le_of_lt ht
    have hd := cost_step_low s hs' t
    have hta := htail (t+1) (by omega)
    change (tail t) ≤ _ at hta
    push_cast at hta
    change tail t ≤ A * ((s : ℝ)^4/a^3 + (s : ℝ)^2/a) at hta
    have hdiv : (s : ℝ)^2/a ≤ (s : ℝ)^4/a^3 := by
      apply (div_le_div_iff₀ ha (by positivity)).2
      calc
        (s : ℝ)^2 * a^3 = a * ((s : ℝ)^2 * a^2) := by ring
        _ ≤ a * ((s : ℝ)^2 * (s : ℝ)^2) := by gcongr
        _ = _ := by ring
    have ht' : tail t ≤ 2 * A * ((s : ℝ)^4/a^3) := by
      nlinarith only [hta, mul_le_mul_of_nonneg_left hdiv hA]
    calc
      _ ≤ tail t * (4*a^3/(s : ℝ)^4) := mul_le_mul_of_nonneg_left hd (by dsimp [tail]; positivity)
      _ ≤ (2*A*((s : ℝ)^4/a^3)) * (4*a^3/(s : ℝ)^4) :=
        mul_le_mul_of_nonneg_right ht' (by positivity)
      _ = _ := by field_simp; ring
  have hhigh (t : ℕ) (ht : s ≤ t) :
      tail t * d t ≤ 8*A * ((s : ℝ)^2 / ((t : ℝ) * (t + 1 : ℝ))) := by
    let a : ℝ := t + 1
    have ht' : 0 < t := hs.trans_le ht
    have htR : (0 : ℝ) < t := by exact_mod_cast ht'
    have ha : 0 < a := by dsimp [a]; positivity
    have ha' : (s : ℝ) ≤ a := by dsimp [a]; exact_mod_cast (show s ≤ t+1 by omega)
    have hd := cost_step_high s hs' t ht'
    have hta := htail (t+1) (by omega)
    change tail t ≤ _ at hta
    push_cast at hta
    change tail t ≤ A * ((s : ℝ)^4/a^3 + (s : ℝ)^2/a) at hta
    have hdiv : (s : ℝ)^4/a^3 ≤ (s : ℝ)^2/a := by
      apply (div_le_div_iff₀ (by positivity) ha).2
      calc
        (s : ℝ)^4 * a = a * ((s : ℝ)^2 * (s : ℝ)^2) := by ring
        _ ≤ a * ((s : ℝ)^2 * a^2) := by gcongr
        _ = _ := by ring
    have ht'' : tail t ≤ 2*A*((s : ℝ)^2/a) := by
      nlinarith only [hta, mul_le_mul_of_nonneg_left hdiv hA]
    calc
      _ ≤ tail t * (4 / (t : ℝ)) := mul_le_mul_of_nonneg_left hd (by dsimp [tail]; positivity)
      _ ≤ (2*A*((s : ℝ)^2/a)) * (4 / (t : ℝ)) :=
        mul_le_mul_of_nonneg_right ht'' (by positivity)
      _ = _ := by change _ = 8*A*((s : ℝ)^2/((t : ℝ)*a)); field_simp; ring
  rw [hid, sum_range_add]
  have hl : ∑ t ∈ range s, tail t * d t ≤ (s : ℝ) * (8*A) := by
    simpa only [sum_const, card_range, nsmul_eq_mul] using
      (sum_le_sum (s := range s) (fun t ht => hlow t (mem_range.mp ht)))
  have hh : ∑ i ∈ range n, tail (s+i) * d (s+i) ≤ (8*A) * (s : ℝ) := by
    calc
      _ ≤ ∑ i ∈ range n, 8*A * ((s : ℝ)^2 / (((s+i : ℕ) : ℝ) * (((s+i+1 : ℕ) : ℝ)))) := by
        apply sum_le_sum
        intro i _
        simpa only [Nat.cast_add, Nat.cast_one] using hhigh (s+i) (by omega)
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_inverse_steps s hs n) (by positivity)
  linarith only [hl, hh]

private theorem log_partition_le {s n : ℕ} (hs : 0 < s) :
    ∑ i ∈ range (s + n), Real.log (1 + (s : ℝ)^4 / (i + 1 : ℝ)^4) ≤ 6 * (s : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  let f (i : ℕ) := Real.log (1 + (s : ℝ)^4 / (i + 1 : ℝ)^4)
  have hlow (i : ℕ) (hi : i < s) : f i ≤ Real.log 2 + 4 * (Real.log s - Real.log (i+1)) := by
    have hp : (0 : ℝ) < i+1 := by positivity
    have hle : (i+1 : ℝ) ≤ s := by exact_mod_cast Nat.succ_le_of_lt hi
    have hratio : 1 ≤ (s : ℝ) ^ 4 / (i + 1 : ℝ) ^ 4 :=
      (le_div_iff₀ (by positivity)).2 (by rw [one_mul]; gcongr)
    unfold f
    calc
      _ ≤ Real.log (2 * ((s : ℝ)^4 / (i+1 : ℝ)^4)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = _ := by
        rw [Real.log_mul (by norm_num) (by positivity : (0 : ℝ) < (s : ℝ)^4 / (i+1 : ℝ)^4).ne',
          Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        ring
  have hlowSum : ∑ i ∈ range s, (Real.log s - Real.log (i+1)) ≤ (s : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (s : ℝ) hs'.le s
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (s : ℝ)^s / s.factorial) h
    rw [Real.log_exp, Real.log_div (by positivity) (by positivity), Real.log_pow] at hlog
    simpa only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      Real.sum_log_add_one_eq_log_factorial] using hlog
  have hl : ∑ i ∈ range s, f i ≤ 5 * (s : ℝ) := by
    have h := sum_le_sum (s := range s) (fun i hi => hlow i (mem_range.mp hi))
    rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at h
    have hlog : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmul := mul_le_mul_of_nonneg_left hlog hs'.le
    linarith only [h, hlowSum, hmul]
  have hh : ∑ i ∈ range n, f (s+i) ≤ (s : ℝ) := by
    refine (sum_le_sum (g := fun i => (s : ℝ)^2 /
      (((s+i : ℕ) : ℝ)*((s+i+1 : ℕ) : ℝ))) ?_).trans (sum_inverse_steps s hs n)
    intro i _
    let a : ℝ := (s+i : ℕ)
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < a+1 := by positivity
    have hsa : (s : ℝ) ≤ a+1 := by dsimp [a]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) i]
    change Real.log (1 + (s : ℝ)^4 / (a+1)^4) ≤ (s : ℝ)^2 / (a * ↑(s+i+1))
    push_cast
    rw [show (s : ℝ) + i + 1 = a+1 by dsimp [a]; push_cast; ring]
    calc
      _ ≤ (s : ℝ)^4 / (a+1)^4 := by
        have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + (s : ℝ)^4 / (a+1)^4)
        linarith only [h]
      _ ≤ (s : ℝ)^2 / (a+1)^2 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        calc
          (s : ℝ)^4 * (a+1)^2 = (s : ℝ)^2 * (a+1)^2 * (s : ℝ)^2 := by ring
          _ ≤ (s : ℝ)^2 * (a+1)^2 * (a+1)^2 := by gcongr
          _ = _ := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        rw [pow_two]
        gcongr
        linarith
  change ∑ i ∈ range (s + n), f i ≤ _
  rw [sum_range_add]
  linarith only [hl, hh]

private theorem sum_counts_mul {N : ℕ} (X : Multiset ℕ)
    (hX : ∀ i ∈ X, 1 ≤ i ∧ i ≤ N) (f : ℕ → ℝ) :
    (∑ i : Fin N, (X.count (i.val + 1) : ℝ) * f (i.val+1)) = (X.map f).sum := by
  induction X using Multiset.induction_on with
  | empty => simp
  | @cons a X ih =>
    have ha := hX a (Multiset.mem_cons_self ..)
    have hX' : ∀ i ∈ X, 1 ≤ i ∧ i ≤ N :=
      fun i hi => hX i (Multiset.mem_cons_of_mem hi)
    have hi : a - 1 < N := by omega
    let k : Fin N := ⟨a-1, hi⟩
    have hk : k.val+1 = a := by dsimp [k]; omega
    have delta (i : Fin N) :
        (((a ::ₘ X).count (i.val+1) : ℕ) : ℝ) * f (i.val+1) =
          (if i = k then f a else 0) + (X.count (i.val+1) : ℝ) * f (i.val+1) := by
      rw [Multiset.count_cons]
      by_cases h : i = k
      · subst i
        simp [hk, add_mul, add_comm]
      · have h' : a ≠ i.val+1 := by
          intro h'
          apply h
          apply Fin.ext
          omega
        simp [h, Ne.symm h']
    simp_rw [delta]
    rw [sum_add_distrib, ih hX']
    simp

private theorem card_of_tail_bound {s n M : ℕ} (hs : 0 < s) (A : ℝ) (hA : 0 ≤ A)
    (S : Set (Multiset ℕ))
    (hcard : ∀ X ∈ S, X.card ≤ M)
    (hX : ∀ X ∈ S, ∀ i ∈ X, 1 ≤ i ∧ i ≤ s + n)
    (htail : ∀ X ∈ S, ∀ i : ℕ, 1 ≤ i →
      ((X.filter (i ≤ ·)).card : ℝ) ≤ A * ((s : ℝ)^4 / (i : ℝ)^3 + (s : ℝ)^2 / i)) :
    (S.ncard : ℝ) ≤ Real.exp ((16 * A + 6) * s) := by
  classical
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  let N := s+n
  let Code := Fin N → Fin (M+1)
  let encode (X : Multiset ℕ) : Code := fun i =>
    ⟨min (X.count (i.val+1)) M, Nat.lt_succ_of_le (min_le_right ..)⟩
  have hencode {X} (hS : X ∈ S) (i : Fin N) :
      (encode X i).val = X.count (i.val+1) :=
    min_eq_left ((Multiset.count_le_card _ _).trans (hcard X hS))
  have hinj : Set.InjOn encode S := by
    intro X h₁ Y h₂ h
    apply Multiset.ext.mpr
    intro i
    by_cases hi : 1 ≤ i ∧ i ≤ N
    · let k : Fin N := ⟨i-1, by omega⟩
      have hk : k.val+1 = i := by dsimp [k]; omega
      have hh := congrArg Fin.val (congrFun h k)
      rwa [hencode h₁, hencode h₂, hk] at hh
    · rw [Multiset.count_eq_zero.mpr (fun h => hi (hX X h₁ i h)),
        Multiset.count_eq_zero.mpr (fun h => hi (hX Y h₂ i h))]
  have hfin : S.Finite := (Set.toFinite (Set.univ : Set Code)).of_injOn (by simp) hinj
  -- Each coding coordinate contributes an independent geometric series.
  let q (i : Fin N) : ℝ := (1 + (i.val + 1 : ℝ)^4 / (s : ℝ)^4)⁻¹
  let weight (f : Code) : ℝ := ∏ i : Fin N, (q i)^((f i).val)
  let T := hfin.toFinset.image encode
  have hT : T.card = S.ncard := by
    rw [card_image_of_injOn (by simpa using hinj), ← Set.ncard_eq_toFinset_card S hfin]
  have hqpos (i : Fin N) : 0 < q i := by dsimp [q]; positivity
  have hqlt (i : Fin N) : q i < 1 := by
    apply inv_lt_one_of_one_lt₀
    have h : 0 < (i.val+1 : ℝ)^4 / (s : ℝ)^4 := by positivity
    linarith
  have hge {f} (hf : f ∈ T) : Real.exp (-(16*A*s)) ≤ weight f := by
    obtain ⟨X, hXf, rfl⟩ := mem_image.mp hf
    have hXS := hfin.mem_toFinset.mp hXf
    have heq (i : Fin N) : q i = Real.exp (-cost s (i.val+1)) := by
      rw [Real.exp_neg]
      simp only [cost, Nat.cast_add, Nat.cast_one, q]
      rw [Real.exp_log (by positivity)]
    have htotal := cost_sum_le hs A hA X (hX X hXS) (htail X hXS)
    unfold weight
    simp_rw [heq, hencode hXS, ← Real.exp_nat_mul, mul_neg]
    rw [← Real.exp_sum, sum_neg_distrib, sum_counts_mul X (hX X hXS)]
    exact Real.exp_le_exp.mpr (neg_le_neg htotal)
  have hlower : Real.exp (-(16*A*s)) * S.ncard ≤ ∑ f : Code, weight f := by
    rw [← hT]
    calc
      _ = ∑ _f ∈ T, Real.exp (-(16*A*s)) := by simp [mul_comm]
      _ ≤ ∑ f ∈ T, weight f := sum_le_sum (fun _ => hge)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
        intro f _ _
        exact prod_nonneg (fun i _ => pow_nonneg (hqpos i).le _))
  have hupper : ∑ f : Code, weight f ≤ Real.exp (6*s) := by
    unfold weight
    have hprod := Fintype.prod_sum (κ := fun _ : Fin N => Fin (M+1))
      (fun i a => q i ^ a.val)
    rw [← hprod]
    have hg (i : Fin N) :
        ∑ a : Fin (M+1), q i ^ a.val ≤ 1 + (s : ℝ)^4/(i.val+1 : ℝ)^4 := by
      rw [Fin.sum_univ_eq_sum_range]
      have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := M+1) (hqpos i).le (hqlt i)
      simp only [Nat.Ico_zero_eq_range, pow_zero] at hgeom
      apply hgeom.trans_eq
      dsimp [q]
      have ha : (i.val + 1 : ℝ) ≠ 0 := by positivity
      have hb : (s : ℝ) ≠ 0 := by positivity
      have hc : (1 + (i.val + 1 : ℝ)^4 / (s : ℝ)^4) ≠ 0 := by positivity
      field_simp
      ring
    calc
      _ ≤ ∏ i : Fin N, (1 + (s : ℝ)^4/(i.val+1 : ℝ)^4) :=
        prod_le_prod₀ (fun i _ => sum_nonneg (fun _ _ => pow_nonneg (hqpos i).le _))
          (fun i _ => hg i)
      _ = Real.exp (∑ i : Fin N, Real.log (1 + (s : ℝ)^4/(i.val+1 : ℝ)^4)) := by
        rw [Real.exp_sum]
        apply prod_congr rfl
        intro i _
        rw [Real.exp_log (by positivity)]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ =>
          Real.log (1 + (s : ℝ)^4/(i+1 : ℝ)^4))]
        exact log_partition_le hs
  calc
    (S.ncard : ℝ) =
      Real.exp (16*A*s) * (Real.exp (-(16*A*s)) * S.ncard) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (16*A*s) * Real.exp (6*s) :=
      mul_le_mul_of_nonneg_left (hlower.trans hupper) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

private theorem rich_line_sizes (P : Finset (ℝ × ℝ)) (hP : 0 < P.card) (k : ℕ) (hk : 2 ≤ k) :
    (((lineSizes P).filter (k ≤ ·)).card : ℝ) ≤
      1024 * ((P.card : ℝ)^2 / (k : ℝ)^3 + (P.card : ℝ) / k) := by
  classical
  obtain ⟨a, hinj⟩ := exists_injective_projection P
  let x (p : ℝ × ℝ) := p.1 + a * p.2
  let lines := (P.offDiag.image (fun pq => line[ℝ, pq.1, pq.2])).filter
    (fun l => k ≤ (P.filter fun r => r ∈ l).card)
  have hrepr (l : lines) : ∃ p q, x p < x q ∧ line[ℝ, p, q] = l.val := by
    have h := (mem_filter.mp l.2).1
    obtain ⟨⟨p, q⟩, hpq, hq⟩ := mem_image.mp h
    obtain ⟨hp, hq', hne⟩ := mem_offDiag.mp hpq
    rcases lt_or_gt_of_ne (fun h => hne (hinj hp hq' h)) with h | h
    · exact ⟨p, q, h, hq⟩
    · exact ⟨q, p, h, AffineSubspace.affineSpan_pair_comm.trans hq⟩
  choose first second hrepr using hrepr
  let code (l : lines) := (edgeSlope x Prod.snd (first l) (second l),
    edgeHeight x Prod.snd (first l) (second l) 0)
  have hcode (l : lines) (p : ℝ × ℝ) :
      p ∈ l.val ↔ p.2 = (code l).1 * x p + (code l).2 := by
    rw [← (hrepr l).2, mem_line_iff_height a (hrepr l).1]
    change edgeHeight x Prod.snd (first l) (second l) (x p) = p.2 ↔ _
    have hh : edgeHeight x Prod.snd (first l) (second l) (x p) =
        (code l).1 * x p + (code l).2 := by dsimp [code, edgeHeight]; ring
    rw [hh, eq_comm]
  have hinjCode : Function.Injective code := by
    intro l m he
    apply Subtype.ext
    apply SetLike.ext
    intro p
    rw [hcode l, hcode m, he]
  let L := (univ : Finset lines).image code
  have hL : L.card = lines.card := by
    rw [card_image_of_injective _ hinjCode, card_univ, Fintype.card_coe]
  have hrich (l : ℝ × ℝ) (hl : l ∈ L) :
      k ≤ ((univ : Finset P).filter (fun p => p.val.2 = l.1 * x p.val + l.2)).card := by
    obtain ⟨z, -, rfl⟩ := mem_image.mp hl
    have hz := (mem_filter.mp z.2).2
    convert hz using 1
    let f : P ↪ ℝ × ℝ := ⟨Subtype.val, Subtype.val_injective⟩
    rw [← card_map f]
    congr 1
    ext p
    simp only [mem_map, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, (hcode z q).mpr hq⟩
    · rintro ⟨hp, hplan⟩
      exact ⟨⟨p, hp⟩, (hcode z p).mp hplan, rfl⟩
  have h := rich_affine_graphs (V := ↥P) (x ∘ Subtype.val) (Prod.snd ∘ Subtype.val)
    (fun p q h => Subtype.ext (hinj p.2 q.2 h)) L k hk (by simpa using hP) hrich
  rw [hL, Fintype.card_coe] at h
  have he : ((lineSizes P).filter (k ≤ ·)).card = lines.card := by
    simp only [lineSizes, Multiset.filter_map, Multiset.card_map]
    rfl
  rw [he]
  exact h

private theorem line_sizes_card_le (P : Finset (ℝ × ℝ)) :
    (lineSizes P).card ≤ P.card * P.card := by
  classical
  simp only [lineSizes, Multiset.card_map, ← Finset.card_def]
  exact card_image_le.trans (by rw [offDiag_card]; omega)

private theorem line_sizes_mem {P : Finset (ℝ × ℝ)} {k : ℕ} (hk : k ∈ lineSizes P) :
    1 ≤ k ∧ k ≤ P.card := by
  classical
  simp only [lineSizes, Multiset.mem_map, ← Finset.mem_def] at hk
  obtain ⟨l, hl, rfl⟩ := hk
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.mp hl
  exact ⟨card_pos.mpr ⟨p, mem_filter.mpr ⟨(mem_offDiag.mp hpq).1,
    left_mem_affineSpan_pair _ _ _⟩⟩, card_filter_le _ _⟩

private theorem count_zero : lineCompatibleCount 0 = 1 := by
  classical
  unfold lineCompatibleCount
  have h : {X : Multiset ℕ | ∃ P : Finset (ℝ × ℝ), P.card = 0 ∧ lineSizes P = X} =
      {(0 : Multiset ℕ)} := by
    ext X
    simp [Finset.card_eq_zero, lineSizes, eq_comm]
  rw [h, Set.ncard_singleton]

/--
**Szemerédi–Trotter bound on line-compatible sequences.** There is a real constant $C$ such that
for every natural number $n$, the number of line-compatible sequences for $n$, that is, of
distinct multisets of the numbers $|\ell \cap P|$ over the distinct lines $\ell$ through two
distinct points of an $n$-point set $P \subseteq \mathbb{R}^2$, each line counted once, is at
most $e^{C \sqrt{n}}$. This answers Erdős Problem 733 with the sequence taken over all
determined lines.

Source: T. F. Bloom, Erdős Problems,
Problem #733, https://www.erdosproblems.com/733 (status PROVED); resolution: E. Szemerédi and W. T.
Trotter, Extremal problems in discrete geometry, Combinatorica 3 (1983), 381-392,
erdosproblems.com/733: 'This is true, and was proved by Szemerédi and Trotter',
https://doi.org/10.1007/BF02579194.
-/
theorem lineCompatibleCountSubexponential_holds : lineCompatibleCountSubexponential := by
  refine ⟨2 * (16 * 1024 + 6), ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [count_zero]
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  let s := n.sqrt + 1
  have hs : 0 < s := by simp [s]
  have hns : (n : ℝ) ≤ (s : ℝ)^2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' n).le
  have hnP : (n : ℝ)^2 ≤ (s : ℝ)^4 := by
    calc
      _ ≤ ((s : ℝ)^2)^2 := by gcongr
      _ = _ := by ring
  have hsqrt : (n.sqrt : ℝ) ≤ Real.sqrt n := by
    have hh : (n.sqrt : ℝ)^2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ)]
  have hone : (1 : ℝ) ≤ Real.sqrt n := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn'
    simpa using Real.sqrt_le_sqrt hnR
  have hscalar : (s : ℝ) ≤ 2 * Real.sqrt n := by dsimp [s]; push_cast; linarith
  have h := card_of_tail_bound (s := s) (n := n) (M := n*n) hs 1024 (by norm_num)
    {X | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ lineSizes P = X}
    (by rintro _ ⟨P, hp, rfl⟩; simpa [hp] using line_sizes_card_le P)
    (by
      rintro _ ⟨P, hp, rfl⟩ i hi
      have h := line_sizes_mem hi
      exact ⟨h.1, (h.2.trans_eq hp).trans (by omega)⟩)
    (by
      rintro _ ⟨P, hp, rfl⟩ k hk
      by_cases hk' : 2 ≤ k
      · have hh := rich_line_sizes P (hp.symm ▸ hn') k hk'
        rw [hp] at hh
        refine hh.trans ?_
        have hkR : (0 : ℝ) < k := by positivity
        gcongr
      · have he : k = 1 := by omega
        subst k
        have hcard := (Multiset.card_le_card (Multiset.filter_le (1 ≤ ·) (lineSizes P))).trans
          (line_sizes_card_le P)
        rw [hp] at hcard
        have hh : (((lineSizes P).filter (1 ≤ ·)).card : ℝ) ≤ (n : ℝ)^2 := by
          rw [pow_two]
          exact_mod_cast hcard
        push_cast
        simp only [one_pow, div_one]
        have hnn : 0 ≤ (s : ℝ)^2 := by positivity
        linarith only [hh, hnP, hnn])
  refine h.trans (Real.exp_le_exp.mpr ?_)
  linarith only [hscalar]

end MathlibExt.Combinatorics.LineCompatibleSequencesErdosProblem733Wanted
