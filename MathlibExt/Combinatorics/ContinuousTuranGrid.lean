/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ContinuousTuran
import Mathlib.Data.Finset.Sort
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.Bertrand

/-!
# Continuous Turán numbers of three-column grids

A grid with three columns and at least three rows has continuous Turán number of order
$n^{5/3}$. The upper bound thickens a planar set to a cylinder and uses the bound for three
stacked plus signs, `opxD_plus_stack_isTheta`. For the lower bound, open squares on the edges of
Brown's graph avoid every grid of this size when their width is smaller than the coordinate gaps.
-/

namespace MetaMathlibExt
namespace opx_grid_three_columns_isTheta

open MeasureTheory Set
open scoped ENNReal

/-- The coordinate map `((x, y), z) ↦ (x, y, z)` preserves Lebesgue measure. -/
private theorem measurePreserving_vec3 :
    MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => ![q.1.1, q.1.2, q.2]) volume volume := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => ![q.1.1, q.1.2, q.2]) := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact measurable_fst.fst
    · exact measurable_fst.snd
    · exact measurable_snd
  refine ⟨hm, ?_⟩
  rw [volume_pi]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun q : (ℝ × ℝ) × ℝ => ![q.1.1, q.1.2, q.2]) ⁻¹' univ.pi s = (s 0 ×ˢ s 1) ×ˢ s 2 := by
    ext q
    simp [Fin.forall_fin_succ, and_assoc]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Fin.prod_univ_three]

-- Use the third coordinate for the columns and the first coordinate for the rows.
private theorem measurePreserving_rotatedCoords :
    MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => ![q.1.2, q.2, q.1.1]) volume volume :=
  measurePreserving_vec3.comp (Measure.measurePreserving_swap.comp
    (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)))

private abbrev stack (r c : ℝ) : Set (Fin 3 → ℝ) :=
  {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}

private theorem cylinder_free {X Y : Finset ℝ} (hX : X.card = 3) {r c : ℝ}
    (hr : 0 ≤ r) (hY : ∀ y ∈ Y, |y| ≤ r) (hc : 0 < c)
    (hgap : ∀ x ∈ X, ∀ x' ∈ X, x' - x ≤ c) {n : ℝ} {S : Set (ℝ × ℝ)}
    (hfree : ¬ PointSetContainsPattern S ((X : Set ℝ) ×ˢ (Y : Set ℝ))) :
    ¬ ContainsPatternD {v : Fin 3 → ℝ | (v 2, v 0) ∈ S ∧ v 1 ∈ Ioo 0 n} (stack r c) := by
  classical
  rintro ⟨f, hf, hmem⟩
  let rank (x : ℝ) : Fin 3 := if hx : x ∈ X then (X.orderIsoOfFin hX).symm ⟨x, hx⟩ else 0
  let z (x : ℝ) := ((rank x : ℕ) + 1 : ℝ) * c
  let v (x y : ℝ) : Fin 3 → ℝ := ![y, 0, z x]
  have hv (x : ℝ) {y : ℝ} (hy : y ∈ Y) : v x y ∈ stack r c := by
    refine ⟨hY y hy, by simpa [v] using hr, Or.inr rfl, (rank x : ℕ) + 1, by omega, ?_, ?_⟩
    · have := (rank x).isLt
      omega
    · simp [v, z]
  apply hfree
  refine ⟨fun x => f 2 (z x), f 0, ?_, ?_, ?_⟩
  · intro p hp q hq hlt
    have hpX : p.1 ∈ X := hp.1
    have hqX : q.1 ∈ X := hq.1
    have hlt' : rank q.1 < rank p.1 := by
      simpa [rank, hpX, hqX] using hlt
    have hstep : ((rank q.1 : ℕ) : ℝ) + 1 ≤ (rank p.1 : ℕ) := by exact_mod_cast hlt'
    have hsep : c ≤ z p.1 - z q.1 := by
      dsimp [z]
      nlinarith [mul_le_mul_of_nonneg_right hstep hc.le]
    exact (hgap _ hqX _ hpX).trans (hsep.trans
      (hf 2 _ (hv p.1 hp.2) _ (hv q.1 hq.2) (show z q.1 < z p.1 by linarith)))
  · intro p hp q hq hlt
    exact hf 0 _ (hv p.1 hp.2) _ (hv q.1 hq.2) hlt
  · intro p hp
    exact (hmem _ (hv p.1 hp.2)).1

-- An open subset of the cube that avoids a pattern has volume at most `opxD 3 n` of the pattern.
private theorem volume_le_opxD {n : ℝ} {T P : Set (Fin 3 → ℝ)} (hT : IsOpen T)
    (hTn : T ⊆ Icc 0 (fun _ => n)) (hP : ¬ ContainsPatternD T P) :
    volume.real T ≤ opxD 3 n P := by
  refine le_csSup ?_ ⟨T, ⟨hT, hTn, hP⟩, rfl⟩
  refine ⟨volume.real (Icc (0 : Fin 3 → ℝ) (fun _ => n)), ?_⟩
  rintro _ ⟨U, ⟨_, hU, _⟩, rfl⟩
  exact measureReal_mono hU isCompact_Icc.measure_ne_top

-- The cylinder over a grid-free planar set avoids three stacked plus signs, so the bound
-- `opx(n, Q_{P,3,c}, 3) = O(n^{8/3})` of `opxD_plus_stack_isTheta` bounds its volume.
private theorem upper {X Y : Finset ℝ} (hX : X.card = 3) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) := by
  classical
  let r := 1 + ∑ a ∈ X ∪ Y, |a|
  have hr : 0 < r := by dsimp [r]; positivity
  have hR {a : ℝ} (ha : a ∈ X ∪ Y) : |a| ≤ r := by
    have := Finset.single_le_sum (f := abs) (fun b _ => abs_nonneg b) ha
    dsimp [r]
    linarith
  let c := 2 * r
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨C, hC0, hC⟩ := ((opxD_plus_stack_isTheta hr hc).2.isBigO.comp_tendsto
    tendsto_natCast_atTop_atTop).exists_pos
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hC.bound, Filter.eventually_ge_atTop 1] with n hCn hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstack : opxD 3 n (stack r c) ≤ C * (n : ℝ) ^ (8 / 3 : ℝ) := by
    simpa only [Function.comp_apply, Real.norm_of_nonneg (opxD_nonneg _ _ _),
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (8 / 3 : ℝ))] using hCn
  rw [Real.norm_of_nonneg (opx_nonneg _ _), Real.norm_of_nonneg (by positivity)]
  apply Real.sSup_le _ (mul_nonneg hC0.le (by positivity))
  rintro _ ⟨S, ⟨hS, hSn, hfree⟩, rfl⟩
  let T := {v : Fin 3 → ℝ | (v 2, v 0) ∈ S ∧ v 1 ∈ Ioo 0 (n : ℝ)}
  have hT : IsOpen T := (hS.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
  have hTn : T ⊆ Icc 0 (fun _ => (n : ℝ)) := by
    intro v hv
    obtain ⟨h2, h0⟩ := hSn hv.1
    have h1 := hv.2
    exact ⟨fun i => by fin_cases i <;> first | exact h0.1 | exact h1.1.le | exact h2.1,
      fun i => by fin_cases i <;> first | exact h0.2 | exact h1.2.le | exact h2.2⟩
  have hfreeT : ¬ ContainsPatternD T (stack r c) := by
    apply cylinder_free hX hr.le (fun y hy => hR (Finset.mem_union_right X hy)) hc _ hfree
    intro x hx x' hx'
    have h1 := (abs_le.mp (hR (Finset.mem_union_left Y hx))).1
    have h2 := (abs_le.mp (hR (Finset.mem_union_left Y hx'))).2
    dsimp [c]
    linarith
  have hvol : volume.real T = (volume S).toReal * n := by
    rw [Measure.real,
      ← measurePreserving_rotatedCoords.measure_preimage hT.measurableSet.nullMeasurableSet]
    change (volume (S ×ˢ Ioo 0 (n : ℝ))).toReal = _
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hn0.le]
  have h := (volume_le_opxD hT hTn hfreeT).trans hstack
  have hpow : (n : ℝ) ^ (8 / 3 : ℝ) = (n : ℝ) ^ (5 / 3 : ℝ) * n := by
    rw [← Real.rpow_add_one hn0.ne']; norm_num
  rw [hvol, hpow, ← mul_assoc] at h
  exact le_of_mul_le_mul_right h hn0

-- One cell width works for all distinct coordinates of the finite pattern.
private theorem exists_width (A : Finset ℝ) :
    ∃ u : ℝ, 0 < u ∧ u ≤ 1 / 64 ∧ ∀ a ∈ A, ∀ b ∈ A, a < b → u ≤ b - a := by
  classical
  let gaps := ((A ×ˢ A).image fun p => p.2 - p.1).filter (0 < ·)
  let D := insert (1 / 64 : ℝ) gaps
  have hD : D.Nonempty := Finset.insert_nonempty _ _
  refine ⟨D.min' hD, ?_, D.min'_le _ (Finset.mem_insert_self ..), ?_⟩
  · rcases Finset.mem_insert.mp (D.min'_mem hD) with h | h
    · rw [h]; norm_num
    · exact (Finset.mem_filter.mp h).2
  · intro a ha b hb hab
    apply D.min'_le
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩, sub_pos.mpr hab⟩)

private theorem floor_lt_floor_of_add_le {a b u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) (hab : a + u ≤ b) :
    ⌊a / u⌋₊ < ⌊b / u⌋₊ := by
  have h1 : a / u + 1 ≤ b / u := by
    rw [div_add_one hu.ne', div_le_div_iff_of_pos_right hu]
    exact hab
  calc ⌊a / u⌋₊ < ⌊a / u⌋₊ + 1 := Nat.lt_succ_self _
    _ = ⌊a / u + 1⌋₊ := (Nat.floor_add_one (div_nonneg ha hu.le)).symm
    _ ≤ ⌊b / u⌋₊ := Nat.floor_le_floor h1

-- An expanding copy of the grid in the union of open cells would use distinct cell
-- indices for three columns and three rows.
private theorem cells_lower {X Y : Finset ℝ} (hX : X.card = 3) (hY : 3 ≤ Y.card)
    {u : ℝ} (hu : 0 < u) (hgap : ∀ a ∈ X ∪ Y, ∀ b ∈ X ∪ Y, a < b → u ≤ b - a)
    {M : ℕ} {E : Finset (ℕ × ℕ)} (hE : ∀ e ∈ E, e.1 < M ∧ e.2 < M)
    (hfree : ∀ I J : Finset ℕ, I.card = 3 → J.card = 3 → ¬ I ×ˢ J ⊆ E) :
    E.card * u ^ 2 ≤ opx (M * u) ((X : Set ℝ) ×ˢ (Y : Set ℝ)) := by
  classical
  let cell (k : ℕ) := Ioo ((k : ℝ) * u) ((k + 1 : ℝ) * u)
  let box (e : ℕ × ℕ) := cell e.1 ×ˢ cell e.2
  let S := ⋃ e ∈ E, box e
  have hbox (e : ℕ × ℕ) : IsOpen (box e) := isOpen_Ioo.prod isOpen_Ioo
  have hS : IsOpen S := isOpen_biUnion fun e _ => hbox e
  have hbound {k : ℕ} (hk : k < M) : cell k ⊆ Icc 0 ((M : ℝ) * u) := by
    intro x hx
    have hk' : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
    exact ⟨(mul_nonneg (Nat.cast_nonneg k) hu.le).trans hx.1.le,
      hx.2.le.trans (mul_le_mul_of_nonneg_right hk' hu.le)⟩
  have hSn : S ⊆ Icc 0 ((M : ℝ) * u) ×ˢ Icc 0 ((M : ℝ) * u) := by
    rintro p hp
    obtain ⟨e, he, hp⟩ := mem_iUnion₂.mp hp
    exact ⟨hbound (hE e he).1 hp.1, hbound (hE e he).2 hp.2⟩
  let idx (x : ℝ) := ⌊x / u⌋₊
  have hidx {k : ℕ} {x : ℝ} (hx : x ∈ cell k) : idx x = k := by
    have h0 := (mul_nonneg (Nat.cast_nonneg k) hu.le).trans hx.1.le
    exact (Nat.floor_eq_iff (div_nonneg h0 hu.le)).mpr
      ⟨(le_div_iff₀ hu).mpr hx.1.le, (div_lt_iff₀ hu).mpr hx.2⟩
  have hdisj : (E : Set (ℕ × ℕ)).PairwiseDisjoint box := by
    intro e _ e' _ hne
    refine disjoint_left.mpr fun p hp hp' => hne ?_
    exact Prod.ext ((hidx hp.1).symm.trans (hidx hp'.1)) ((hidx hp.2).symm.trans (hidx hp'.2))
  have hvol : volume.real S = E.card * u ^ 2 := by
    have hcell (k : ℕ) : volume (cell k) = ENNReal.ofReal u := by
      change volume (Ioo _ _) = _
      rw [Real.volume_Ioo]
      congr 1
      ring
    have hvolbox (e : ℕ × ℕ) : volume (box e) = ENNReal.ofReal u ^ 2 := by
      change volume (cell e.1 ×ˢ cell e.2) = _
      rw [Measure.volume_eq_prod, Measure.prod_prod, hcell, hcell, sq]
    rw [Measure.real, measure_biUnion_finset hdisj fun e _ => (hbox e).measurableSet]
    simp [hvolbox, ENNReal.toReal_mul, ENNReal.toReal_pow, hu.le]
  have hfreeS : ¬ PointSetContainsPattern S ((X : Set ℝ) ×ˢ (Y : Set ℝ)) := by
    rintro ⟨f, g, hf, hg, himg⟩
    have hcell {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) : (idx (f x), idx (g y)) ∈ E := by
      obtain ⟨e, he, hp⟩ := mem_iUnion₂.mp (himg (x, y) ⟨hx, hy⟩)
      rwa [hidx hp.1, hidx hp.2]
    obtain ⟨Y', hsub, hY'⟩ := Finset.exists_subset_card_eq hY
    obtain ⟨x₀, hx₀⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y₀, hy₀⟩ : Y.Nonempty := Finset.card_pos.mp (by omega)
    have hcol : StrictMonoOn (idx ∘ f) (X : Set ℝ) := by
      intro x hx x' hx' hlt
      have he := hf (x', y₀) ⟨hx', hy₀⟩ (x, y₀) ⟨hx, hy₀⟩ hlt
      have hd := hgap x (Finset.mem_union_left _ hx) x' (Finset.mem_union_left _ hx') hlt
      exact floor_lt_floor_of_add_le hu (hSn (himg (x, y₀) ⟨hx, hy₀⟩)).1.1 (by linarith)
    have hrow : StrictMonoOn (idx ∘ g) (Y' : Set ℝ) := by
      intro y hy y' hy' hlt
      have he := hg (x₀, y') ⟨hx₀, hsub hy'⟩ (x₀, y) ⟨hx₀, hsub hy⟩ hlt
      have hd := hgap y (Finset.mem_union_right _ (hsub hy)) y'
        (Finset.mem_union_right _ (hsub hy')) hlt
      exact floor_lt_floor_of_add_le hu (hSn (himg (x₀, y) ⟨hx₀, hsub hy⟩)).2.1 (by linarith)
    apply hfree (X.image (idx ∘ f)) (Y'.image (idx ∘ g))
      ((Finset.card_image_of_injOn hcol.injOn).trans hX)
      ((Finset.card_image_of_injOn hrow.injOn).trans hY')
    rintro ⟨i, j⟩ hij
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hij).1
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hij).2
    exact hcell hx (hsub hy)
  rw [← hvol]
  refine le_csSup ?_ ⟨S, ⟨hS, hSn, hfreeS⟩, rfl⟩
  refine ⟨volume.real (Icc 0 ((M : ℝ) * u) ×ˢ Icc 0 ((M : ℝ) * u)), ?_⟩
  rintro _ ⟨T, ⟨_, hT, _⟩, rfl⟩
  exact measureReal_mono hT (isCompact_Icc.prod isCompact_Icc).measure_ne_top

/-! ### Brown's graph

Brown's `K_{3,3}`-free graph on `𝔽_p³` joins `a` and `b` when `b - a` lies on a sphere of
nonsquare radius. The lemmas below repeat the private helpers of the lower bound of
`opxD_plus_stack_isTheta` in `MathlibExt.Combinatorics.ContinuousTuran`, so that this file uses
only the public declarations of that module. -/

/-- A relation on a finite type without `t × t` grids gives a set of cells of the same size,
inside `{0, …, |V| - 1}²`, without `t × t` grids. -/
private theorem exists_cells {V : Type*} [Fintype V] (R : V → V → Prop) [DecidableRel R] {t : ℕ}
    (hR : ∀ A B : Finset V, A.card = t → B.card = t → ¬ ∀ a ∈ A, ∀ b ∈ B, R a b) :
    ∃ E : Finset (ℕ × ℕ), (∀ e ∈ E, e.1 < Fintype.card V ∧ e.2 < Fintype.card V) ∧
      E.card = (Finset.univ.filter fun ab : V × V => R ab.1 ab.2).card ∧
      ∀ I J : Finset ℕ, I.card = t → J.card = t → ¬ I ×ˢ J ⊆ E := by
  classical
  let enc : V → ℕ := fun a => (Fintype.equivFin V a : ℕ)
  have henc : Function.Injective enc := fun a b h => (Fintype.equivFin V).injective (Fin.ext h)
  let encp : V × V → ℕ × ℕ := fun ab => (enc ab.1, enc ab.2)
  have hencp : Function.Injective encp := fun x y h =>
    Prod.ext (henc (congrArg Prod.fst h)) (henc (congrArg Prod.snd h))
  refine ⟨(Finset.univ.filter fun ab : V × V => R ab.1 ab.2).image encp, ?_,
    Finset.card_image_of_injective _ hencp, ?_⟩
  · intro e he
    obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 he
    exact ⟨(Fintype.equivFin V ab.1).2, (Fintype.equivFin V ab.2).2⟩
  · intro I J hI hJ hIJ
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact hR ∅ ∅ rfl rfl (by simp)
    have hrange : ∀ {I J : Finset ℕ}, J.card = t → (∀ i ∈ I, ∀ j ∈ J, (i, j) ∈ (Finset.univ.filter
        fun ab : V × V => R ab.1 ab.2).image encp) → (Finset.univ.filter fun a => enc a ∈ I).image
        enc = I := by
      intro I J hJ hIJ
      ext i
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hi
        obtain ⟨j, hj⟩ : J.Nonempty := by rw [← Finset.card_pos, hJ]; exact ht
        obtain ⟨ab, -, hab⟩ := Finset.mem_image.1 (hIJ i hi j hj)
        have hab1 : enc ab.1 = i := congrArg Prod.fst hab
        exact ⟨ab.1, by rw [hab1]; exact hi, hab1⟩
    have hIJ' : ∀ i ∈ I, ∀ j ∈ J, (i, j) ∈ (Finset.univ.filter
        fun ab : V × V => R ab.1 ab.2).image encp := fun i hi j hj =>
      hIJ (Finset.mem_product.2 ⟨hi, hj⟩)
    have hJI' : ∀ j ∈ J, ∀ i ∈ I, (i, j) ∈ (Finset.univ.filter
        fun ab : V × V => R ab.1 ab.2).image encp := fun j hj i hi => hIJ' i hi j hj
    have hA := hrange hJ hIJ'
    have hB : (Finset.univ.filter fun b => enc b ∈ J).image enc = J := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact hb
      · intro hj
        obtain ⟨i, hi⟩ : I.Nonempty := by rw [← Finset.card_pos, hI]; exact ht
        obtain ⟨ab, -, hab⟩ := Finset.mem_image.1 (hJI' j hj i hi)
        have hab2 : enc ab.2 = j := congrArg Prod.snd hab
        exact ⟨ab.2, by rw [hab2]; exact hj, hab2⟩
    refine hR (Finset.univ.filter fun a => enc a ∈ I) (Finset.univ.filter fun b => enc b ∈ J)
      (by rw [← Finset.card_image_of_injective _ henc, hA, hI])
      (by rw [← Finset.card_image_of_injective _ henc, hB, hJ]) ?_
    intro a ha b hb
    obtain ⟨ab, hab, heq⟩ := Finset.mem_image.1
      (hIJ' _ (Finset.mem_filter.1 ha).2 _ (Finset.mem_filter.1 hb).2)
    have : ab = (a, b) := hencp heq
    subst this
    exact (Finset.mem_filter.1 hab).2

section Brown

variable {F : Type*} [Field F]

/-- The quadratic form `w₀ w₁ + w₂²` on `F³`, whose level sets are the spheres of Brown's
`K_{3,3}`-free graph. -/
private def brownQ (w : Fin 3 → F) : F := w 0 * w 1 + w 2 ^ 2

/-- The polar form of `brownQ`. -/
private def brownB (u w : Fin 3 → F) : F := u 0 * w 1 + u 1 * w 0 + 2 * (u 2 * w 2)

/-- The linear map with `brownB u w = brownM u ⬝ᵥ w`. -/
private def brownM (w : Fin 3 → F) : Fin 3 → F := ![w 1, w 0, 2 * w 2]

private theorem brownQ_sub (u w : Fin 3 → F) :
    brownQ (u - w) = brownQ u + brownQ w - brownB u w := by
  simp only [brownQ, brownB, Pi.sub_apply]
  ring

private theorem brownQ_sub_smul (v A : Fin 3 → F) (l : F) :
    brownQ (v - l • A) = brownQ v + l ^ 2 * brownQ A - l * brownB v A := by
  simp only [brownQ, brownB, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem brownQ_neg (w : Fin 3 → F) : brownQ (-w) = brownQ w := by
  simp only [brownQ, Pi.neg_apply]
  ring

private theorem brownB_eq_dotProduct (u w : Fin 3 → F) : brownB u w = brownM u ⬝ᵥ w := by
  simp only [brownB, brownM, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem brownB_sub_sub (a a' b b' : Fin 3 → F) :
    brownB (b' - b) (a' - a) =
      brownQ (b - a') + brownQ (b' - a) - brownQ (b - a) - brownQ (b' - a') := by
  simp only [brownB, brownQ, Pi.sub_apply]
  ring

/-- On the plane orthogonal to a nonzero isotropic vector, `brownQ` takes only square values. -/
private theorem isSquare_brownQ {u w : Fin 3 → F} (hw : w ≠ 0) (hQ : brownQ w = 0)
    (hB : brownB u w = 0) : IsSquare (brownQ u) := by
  simp only [brownQ, brownB] at hQ hB ⊢
  by_cases h0 : w 0 = 0
  · by_cases h1 : w 1 = 0
    · exfalso
      apply hw
      ext i
      fin_cases i
      · exact h0
      · exact h1
      · simp only [h0, h1, zero_mul, zero_add, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true] at hQ
        exact hQ
    · refine ⟨(u 1 * w 2 - u 2 * w 1) / w 1, ?_⟩
      field_simp
      linear_combination (-(u 1) ^ 2) * hQ + (u 1 * w 1) * hB
  · refine ⟨(u 0 * w 2 - u 2 * w 0) / w 0, ?_⟩
    field_simp
    linear_combination (-(u 0) ^ 2) * hQ + (u 0 * w 0) * hB

/-- Three collinear points `v, v - A, v - l A` cannot all lie on the sphere `brownQ = r` with
`r` a nonsquare: such a sphere contains no line. -/
private theorem brown_collinear {r : F} (hr : ¬ IsSquare r) {v A : Fin 3 → F} {l : F}
    (hA : A ≠ 0) (hl0 : l ≠ 0) (hl1 : l ≠ 1) (h1 : brownQ v = r) (h2 : brownQ (v - A) = r)
    (h3 : brownQ (v - l • A) = r) : False := by
  rw [brownQ_sub] at h2
  rw [brownQ_sub_smul] at h3
  have hQA : brownQ A = brownB v A := by linear_combination h2 - h1
  have hQA0 : brownQ A = 0 := by
    have : l * (l - 1) * brownQ A = 0 := by linear_combination h3 - h1 - l * hQA
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hl0
      · exact absurd (sub_eq_zero.1 h) hl1
    · exact h
  exact hr (h1 ▸ isSquare_brownQ hA hQA0 (hQA ▸ hQA0))

/-- If `X × Y = 0` with `X ≠ 0`, then `Y` is a multiple of `X`. -/
private theorem exists_smul_of_cross_eq_zero {X Y : Fin 3 → F} (hX : X ≠ 0)
    (h : crossProduct X Y = 0) : ∃ l : F, Y = l • X := by
  rw [cross_apply] at h
  have h0 : X 1 * Y 2 - X 2 * Y 1 = 0 := by simpa using congrFun h 0
  have h1 : X 2 * Y 0 - X 0 * Y 2 = 0 := by simpa using congrFun h 1
  have h2 : X 0 * Y 1 - X 1 * Y 0 = 0 := by simpa using congrFun h 2
  by_cases hx0 : X 0 = 0
  · by_cases hx1 : X 1 = 0
    · have hx2 : X 2 ≠ 0 := fun hx2 => hX (by ext i; fin_cases i <;> simp [hx0, hx1, hx2])
      refine ⟨Y 2 / X 2, ?_⟩
      ext i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Pi.smul_apply, smul_eq_mul] <;> field_simp
      · simp only [hx0, zero_mul, sub_zero, mul_eq_zero, hx2, false_or] at h1
        simp [h1, hx0]
      · simp only [hx1, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero, hx2, false_or] at h0
        simp [h0, hx1]
    · refine ⟨Y 1 / X 1, ?_⟩
      ext i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Pi.smul_apply, smul_eq_mul] <;> field_simp
      · simp only [hx0, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero, hx1, false_or] at h2
        simp [h2, hx0]
      · linear_combination h0
  · refine ⟨Y 0 / X 0, ?_⟩
    ext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Pi.smul_apply, smul_eq_mul] <;> field_simp
    · linear_combination h2
    · linear_combination -h1

/-- **Brown's construction.** Distinct points `a₁, a₂, a₃` and `b₁, b₂, b₃` of `F³` (with
`2 ≠ 0` in `F`) cannot satisfy `brownQ (b_j - a_i) = r` for all `i, j` when `r` is a
nonsquare. -/
private theorem brown_free (h2 : (2 : F) ≠ 0) {r : F} (hr : ¬ IsSquare r) :
    ∀ A B : Finset (Fin 3 → F), A.card = 3 → B.card = 3 →
      ¬ ∀ a ∈ A, ∀ b ∈ B, brownQ (b - a) = r := by
  classical
  intro A B hA hB h
  obtain ⟨a1, a2, a3, ha12, ha13, ha23, rfl⟩ := Finset.card_eq_three.1 hA
  obtain ⟨b1, b2, b3, hb12, hb13, hb23, rfl⟩ := Finset.card_eq_three.1 hB
  have h11 := h a1 (by simp) b1 (by simp)
  have h12 := h a1 (by simp) b2 (by simp)
  have h13 := h a1 (by simp) b3 (by simp)
  have h21 := h a2 (by simp) b1 (by simp)
  have h22 := h a2 (by simp) b2 (by simp)
  have h23 := h a2 (by simp) b3 (by simp)
  have h31 := h a3 (by simp) b1 (by simp)
  have h32 := h a3 (by simp) b2 (by simp)
  have h33 := h a3 (by simp) b3 (by simp)
  have hor : ∀ {a a' b b' : Fin 3 → F}, brownQ (b - a) = r → brownQ (b - a') = r →
      brownQ (b' - a) = r → brownQ (b' - a') = r → brownB (b' - b) (a' - a) = 0 := by
    intro a a' b b' e1 e2 e3 e4
    rw [brownB_sub_sub, e1, e2, e3, e4]
    ring
  have hA2 : a2 - a1 ≠ 0 := sub_ne_zero.2 (Ne.symm ha12)
  have hA3 : a3 - a1 ≠ 0 := sub_ne_zero.2 (Ne.symm ha13)
  have hB2 : b2 - b1 ≠ 0 := sub_ne_zero.2 (Ne.symm hb12)
  by_cases hC : crossProduct (a2 - a1) (a3 - a1) = 0
  · obtain ⟨l, hl⟩ := exists_smul_of_cross_eq_zero hA2 hC
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hA3 (by simpa using hl)
    have hl1 : l ≠ 1 := by
      rintro rfl
      exact ha23 (by simpa using hl.symm)
    refine brown_collinear hr hA2 hl0 hl1 h11 ?_ ?_
    · rw [show b1 - a1 - (a2 - a1) = b1 - a2 by abel]
      exact h21
    · rw [← hl, show b1 - a1 - (a3 - a1) = b1 - a3 by abel]
      exact h31
  · have hX : ∀ {b' : Fin 3 → F}, brownB (b' - b1) (a2 - a1) = 0 →
        brownB (b' - b1) (a3 - a1) = 0 →
        crossProduct (crossProduct (a2 - a1) (a3 - a1)) (brownM (b' - b1)) = 0 := by
      intro b' e2 e3
      rw [brownB_eq_dotProduct] at e2 e3
      rw [← cross_anticomm, cross_cross_eq_smul_sub_smul', dotProduct_comm (a2 - a1), e2, e3]
      simp
    obtain ⟨μ2, hμ2⟩ := exists_smul_of_cross_eq_zero hC
      (hX (hor h11 h21 h12 h22) (hor h11 h31 h12 h32))
    obtain ⟨μ3, hμ3⟩ := exists_smul_of_cross_eq_zero hC
      (hX (hor h11 h21 h13 h23) (hor h11 h31 h13 h33))
    have hM : ∀ w : Fin 3 → F, brownM w = 0 → w = 0 := by
      intro w hw
      have e0 := congrFun hw 0
      have e1 := congrFun hw 1
      have e2 := congrFun hw 2
      simp only [brownM, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply, mul_eq_zero, h2, false_or] at e0 e1 e2
      ext i
      fin_cases i
      · exact e1
      · exact e0
      · exact e2
    have hμ2' : μ2 ≠ 0 := by
      rintro rfl
      exact hB2 (hM _ (by simpa using hμ2))
    set l := μ3 / μ2 with hl_def
    have hl : b3 - b1 = l • (b2 - b1) := by
      have : brownM (b3 - b1 - l • (b2 - b1)) = 0 := by
        have hlin : brownM (b3 - b1 - l • (b2 - b1)) =
            brownM (b3 - b1) - l • brownM (b2 - b1) := by
          ext i
          fin_cases i
          · simp [brownM]
          · simp [brownM]
          · simp [brownM]
            ring
        rw [hlin, hμ2, hμ3, smul_smul, hl_def, div_mul_cancel₀ _ hμ2', sub_self]
      exact sub_eq_zero.1 (hM _ this)
    have hl0 : l ≠ 0 := by
      rintro h0
      rw [h0, zero_smul, sub_eq_zero] at hl
      exact hb13 hl.symm
    have hl1 : l ≠ 1 := by
      rintro h1
      rw [h1, one_smul, sub_left_inj] at hl
      exact hb23 hl.symm
    refine brown_collinear hr hB2 hl0 hl1 (v := a1 - b1) ?_ ?_ ?_
    · rw [← brownQ_neg, neg_sub]
      exact h11
    · rw [show a1 - b1 - (b2 - b1) = -(b2 - a1) by abel, brownQ_neg]
      exact h12
    · rw [← hl, show a1 - b1 - (b3 - b1) = -(b3 - a1) by abel, brownQ_neg]
      exact h13

end Brown

/-- Brown's graph has at least `q³ (q - 1) q` edges: from every `a`, the points
`a + (x, (r - z²) / x, z)` with `x ≠ 0` lie on the sphere `brownQ (b - a) = r`. -/
private theorem card_brown {F : Type*} [Field F] [Fintype F] [DecidableEq F] (r : F) :
    Fintype.card F ^ 3 * ((Fintype.card F - 1) * Fintype.card F) ≤
      (Finset.univ.filter fun ab : (Fin 3 → F) × (Fin 3 → F) =>
        brownQ (ab.2 - ab.1) = r).card := by
  let φ : (Fin 3 → F) × F × F → (Fin 3 → F) × (Fin 3 → F) :=
    fun axz => (axz.1, axz.1 + ![axz.2.1, (r - axz.2.2 ^ 2) / axz.2.1, axz.2.2])
  have hφ : Function.Injective φ := by
    rintro ⟨a, x, z⟩ ⟨a', x', z'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, add_right_inj] at h0 h2
    rw [h0, h2]
  let D : Finset ((Fin 3 → F) × F × F) :=
    Finset.univ ×ˢ ((Finset.univ.filter fun x : F => x ≠ 0) ×ˢ Finset.univ)
  have hD : D.card = Fintype.card F ^ 3 * ((Fintype.card F - 1) * Fintype.card F) := by
    simp only [D, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [Finset.filter_ne' Finset.univ (0 : F), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  calc _ = D.card := hD.symm
    _ = (D.image φ).card := (Finset.card_image_of_injective _ hφ).symm
    _ ≤ _ := Finset.card_le_card fun ab hab => by
        obtain ⟨⟨a, x, z⟩, hxz, rfl⟩ := Finset.mem_image.1 hab
        have hx : x ≠ 0 := (Finset.mem_filter.1 (Finset.mem_product.1
          (Finset.mem_product.1 hxz).2).1).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, φ, add_sub_cancel_left]
        simp only [brownQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        field_simp
        ring

-- Bertrand's postulate supplies a Brown graph with between n and 64n vertices on each side.
private theorem lower {X Y : Finset ℝ} (hX : X.card = 3) (hY : 3 ≤ Y.card) :
    (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) := by
  classical
  obtain ⟨u, hu, hu64, hgap⟩ := exists_width (X ∪ Y)
  refine Asymptotics.IsBigO.of_bound (2 / u ^ 2) ?_
  filter_upwards [Filter.eventually_ge_atTop 8] with n hn
  let s := (n : ℝ) ^ (1 / 3 : ℝ)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs3 : s ^ 3 = n := by
    dsimp only [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hs2 : 2 ≤ s :=
    le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) hs (by rw [hs3]; norm_num; exact hn)
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈s⌉₊
    (Nat.ceil_pos.2 (by linarith)).ne'
  have := Fact.mk hp
  have hps : s ≤ p := (Nat.le_ceil s).trans (by exact_mod_cast hmp.le)
  have hp3 : 3 ≤ p := by
    have h : (2 : ℝ) < p := (hs2.trans (Nat.le_ceil s)).trans_lt (by exact_mod_cast hmp)
    exact_mod_cast h
  have hp4 : (p : ℝ) ≤ 4 * s := by
    have h : (p : ℝ) ≤ 2 * ⌈s⌉₊ := by exact_mod_cast hp2m
    linarith [Nat.ceil_lt_add_one hs]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨ρ, hρ⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  obtain ⟨E, hE, hEcard, hEfree⟩ := exists_cells (V := Fin 3 → ZMod p)
    (fun a b => brownQ (b - a) = ρ) (brown_free h2 hρ)
  have hcardV : Fintype.card (Fin 3 → ZMod p) = p ^ 3 := by simp [ZMod.card]
  rw [hcardV] at hE
  have hfit : ((p ^ 3 : ℕ) : ℝ) * u ≤ n := by
    push_cast
    calc (p : ℝ) ^ 3 * u ≤ (4 * s) ^ 3 * (1 / 64) := by gcongr
      _ = (n : ℝ) := by rw [← hs3]; ring
  have harea := (cells_lower hX hY hu hgap hE hEfree).trans (opx_mono_left _ hfit)
  have hcount : (p : ℝ) ^ 3 * (((p : ℝ) - 1) * p) ≤ E.card := by
    rw [hEcard]
    have h := card_brown (F := ZMod p) ρ
    rw [ZMod.card] at h
    calc (p : ℝ) ^ 3 * ((p - 1) * p) = ((p ^ 3 * ((p - 1) * p) : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub hp.one_le]
          ring
      _ ≤ _ := by exact_mod_cast h
  have hpow : (n : ℝ) ^ (5 / 3 : ℝ) = s ^ 5 := by
    dsimp only [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hhalf : (p : ℝ) / 2 ≤ p - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have hcard : s ^ 5 / 2 ≤ E.card := calc
    s ^ 5 / 2 ≤ (p : ℝ) ^ 5 / 2 := by gcongr
    _ = (p : ℝ) ^ 3 * ((p / 2) * p) := by ring
    _ ≤ _ := (by gcongr : (p : ℝ) ^ 3 * ((p / 2) * p) ≤ p ^ 3 * ((p - 1) * p))
    _ ≤ _ := hcount
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (opx_nonneg _ _), hpow,
    div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hu)]
  linarith [mul_le_mul_of_nonneg_right hcard (sq_nonneg u)]

end opx_grid_three_columns_isTheta

/-- **Continuous Turán number of a grid with three columns.** Let $X$ and $Y$ be finite sets of
real numbers with $|X| = 3$ and $|Y| \ge 3$, and let $P = X \times Y$ be the grid with $3$ columns
and $|Y|$ rows. Then $\operatorname{opx}(n, P) = \Theta(n^{5/3})$ as the natural number $n$ tends
to infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.7
(`integers-2024-A1-cor-3-7`), second sentence. -/
public theorem opx_grid_three_columns_isTheta {X Y : Finset ℝ} (hX : X.card = 3)
    (hY : 3 ≤ Y.card) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) :=
  ⟨opx_grid_three_columns_isTheta.upper hX, opx_grid_three_columns_isTheta.lower hX hY⟩

end MetaMathlibExt
