/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPolygonTurning
import Code.FrontierA.KacWardFourSignMajority
import Code.FrontierA.KacWardHalfPlaneSegment
import Code.FrontierA.KacWardInteriorSideSplice
import Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate










namespace StatMech.FrontierA

theorem kw_sbtw_iff_mem_openSegment {x y z : ℂ} (hxz : x ≠ z) :
    Sbtw ℝ x y z ↔ y ∈ openSegment ℝ x z := by
  constructor
  · intro h
    rw [openSegment_eq_image_lineMap]
    exact h.mem_image_Ioo
  · intro h
    rw [openSegment_eq_image_lineMap] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact sbtw_lineMap_iff.mpr ⟨hxz, ht⟩



theorem kw_sbtw_eq_or_sbtw_or_sbtw {a b c z : ℂ}
    (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c)
    (hbetween : Wbtw ℝ a b c) (hz : Sbtw ℝ a z c) :
    z = b ∨ Sbtw ℝ a z b ∨ Sbtw ℝ b z c := by
  have hbline : b ∈ Set.range (AffineMap.lineMap a c : ℝ → ℂ) := by
    rcases hbetween with ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  have hzmem : z ∈ openSegment ℝ a c :=
    (kw_sbtw_iff_mem_openSegment hac).mp hz
  rcases openSegment_subset_union a c hbline hzmem with hzB | hzleft | hzright
  · exact Or.inl hzB
  · exact Or.inr <| Or.inl <|
      (kw_sbtw_iff_mem_openSegment hab).mpr hzleft
  · exact Or.inr <| Or.inr <|
      (kw_sbtw_iff_mem_openSegment hbc).mpr hzright

theorem kwComplexCross_add_right (a b c : ℂ) :
    kwComplexCross a (b + c) =
      kwComplexCross a b + kwComplexCross a c := by
  unfold kwComplexCross
  simp only [Complex.add_re, Complex.add_im]
  ring

theorem kwComplexCross_sub_right (a b c : ℂ) :
    kwComplexCross a (b - c) =
      kwComplexCross a b - kwComplexCross a c := by
  unfold kwComplexCross
  simp only [Complex.sub_re, Complex.sub_im]
  ring

theorem kwComplexCross_mul_real_left (r : ℝ) (a b : ℂ) :
    kwComplexCross ((r : ℂ) * a) b = r * kwComplexCross a b := by
  unfold kwComplexCross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem kwComplexCross_mul_real_right (r : ℝ) (a b : ℂ) :
    kwComplexCross a ((r : ℂ) * b) = r * kwComplexCross a b := by
  unfold kwComplexCross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

@[simp] theorem kwComplexCross_self (a : ℂ) :
    kwComplexCross a a = 0 := by
  unfold kwComplexCross
  ring

theorem kwComplexCross_swap (a b : ℂ) :
    kwComplexCross a b = -kwComplexCross b a := by
  unfold kwComplexCross
  ring

@[simp] theorem kwComplexCross_neg_right (a b : ℂ) :
    kwComplexCross a (-b) = -kwComplexCross a b := by
  unfold kwComplexCross
  simp
  ring




theorem kw_exists_common_sbtw_of_cross_opposite {A B C D : ℂ}
    (hAB : kwComplexCross (B - A) (C - A) *
        kwComplexCross (B - A) (D - A) < 0)
    (hCD : kwComplexCross (D - C) (A - C) *
        kwComplexCross (D - C) (B - C) < 0) :
    ∃ z : ℂ, Sbtw ℝ A z B ∧ Sbtw ℝ C z D := by
  let a := B - A
  let c := D - C
  let x := kwComplexCross c (A - C)
  let y := kwComplexCross a (C - A)
  let den := kwComplexCross a c
  have hABD : kwComplexCross a (D - A) = y + den := by
    dsimp only [a, c, y, den]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hCDB : kwComplexCross c (B - C) = x - den := by
    dsimp only [a, c, x, den]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hxy : y * (y + den) < 0 := by
    simpa only [a, y, hABD] using hAB
  have hxx : x * (x - den) < 0 := by
    simpa only [c, x, hCDB] using hCD
  have hden : den ≠ 0 := by
    intro hz
    rw [hz] at hxy
    norm_num at hxy
    nlinarith [sq_nonneg y]
  let t : ℝ := x / den
  let u : ℝ := -y / den
  have interval_div (v : ℝ) (hv : v * (v - den) < 0) :
      v / den ∈ Set.Ioo (0 : ℝ) 1 := by
    rcases lt_or_gt_of_ne hden with hdneg | hdpos
    · have hvneg : v < 0 := by
        by_contra hn
        have hv0 : 0 ≤ v := le_of_not_gt hn
        have hvd0 : 0 ≤ v - den := by linarith
        exact (not_lt_of_ge (mul_nonneg hv0 hvd0)) hv
      have hdv : den < v := by
        by_contra hn
        have hvd : v ≤ den := le_of_not_gt hn
        have hv0 : v ≤ 0 := le_trans hvd hdneg.le
        have hvd0 : v - den ≤ 0 := sub_nonpos.mpr hvd
        exact (not_lt_of_ge
          (mul_nonneg_of_nonpos_of_nonpos hv0 hvd0)) hv
      exact ⟨div_pos_of_neg_of_neg hvneg hdneg,
        (div_lt_one_of_neg hdneg).mpr hdv⟩
    · have hvpos : 0 < v := by
        by_contra hn
        have hv0 : v ≤ 0 := le_of_not_gt hn
        have hvd0 : v - den ≤ 0 := by linarith
        exact (not_lt_of_ge
          (mul_nonneg_of_nonpos_of_nonpos hv0 hvd0)) hv
      have hvd : v < den := by
        by_contra hn
        have hdv : den ≤ v := le_of_not_gt hn
        have hv0 : 0 ≤ v := le_trans hdpos.le hdv
        have hvd0 : 0 ≤ v - den := sub_nonneg.mpr hdv
        exact (not_lt_of_ge (mul_nonneg hv0 hvd0)) hv
      exact ⟨div_pos hvpos hdpos, (div_lt_one hdpos).mpr hvd⟩
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := interval_div x hxx
  have hu : u ∈ Set.Ioo (0 : ℝ) 1 := by
    apply interval_div (-y)
    nlinarith [hxy]
  let w : ℂ := (t : ℂ) * a - (u : ℂ) * c - (C - A)
  have haw : kwComplexCross a w = 0 := by
    calc
      kwComplexCross a w = -(u * den) - y := by
        dsimp only [w]
        rw [kwComplexCross_sub_right, kwComplexCross_sub_right,
          kwComplexCross_mul_real_right, kwComplexCross_mul_real_right,
          kwComplexCross_self]
        dsimp only [den, y]
        ring
      _ = 0 := by
        dsimp only [u]
        field_simp [hden]
        ring
  have hcw : kwComplexCross c w = 0 := by
    calc
      kwComplexCross c w = -(t * den) + x := by
        dsimp only [w]
        rw [kwComplexCross_sub_right, kwComplexCross_sub_right,
          kwComplexCross_mul_real_right, kwComplexCross_mul_real_right,
          kwComplexCross_self, kwComplexCross_swap]
        have hneg : C - A = -(A - C) := by ring
        rw [hneg, kwComplexCross_neg_right]
        dsimp only [den, x]
        ring
      _ = 0 := by
        dsimp only [t]
        field_simp [hden]
        ring
  have hwre : w.re = 0 := by
    have hprod : den * w.re = 0 := by
      dsimp only [den]
      unfold kwComplexCross at haw hcw ⊢
      linear_combination c.re * haw - a.re * hcw
    exact (mul_eq_zero.mp hprod).resolve_left hden
  have hwim : w.im = 0 := by
    have hprod : den * w.im = 0 := by
      dsimp only [den]
      unfold kwComplexCross at haw hcw ⊢
      linear_combination c.im * haw - a.im * hcw
    exact (mul_eq_zero.mp hprod).resolve_left hden
  have hw : w = 0 := Complex.ext hwre hwim
  have hAC : C - A = (t : ℂ) * a - (u : ℂ) * c := by
    dsimp only [w] at hw
    rw [sub_eq_zero] at hw
    exact hw.symm
  have hline : AffineMap.lineMap A B t = AffineMap.lineMap C D u := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    change (t : ℂ) * (B - A) + A = (u : ℂ) * (D - C) + C
    rw [show B - A = a by rfl, show D - C = c by rfl]
    rw [show C = (C - A) + A by ring, hAC]
    ring
  refine ⟨AffineMap.lineMap A B t, ?_, ?_⟩
  · exact sbtw_lineMap_iff.mpr ⟨(by
      intro hab
      subst B
      simp [kwComplexCross] at hAB), ht⟩
  · rw [hline]
    exact sbtw_lineMap_iff.mpr ⟨(by
      intro hcd
      subst D
      simp [kwComplexCross] at hCD), hu⟩



theorem kwComplexCross_eq_zero_of_sbtw {A B C : ℂ}
    (h : Sbtw ℝ A B C) :
    kwComplexCross (C - A) (B - A) = 0 := by
  obtain ⟨t, ht, htEq⟩ := h.mem_image_Ioo
  have heq := congrArg
    (fun w : ℂ ↦ kwComplexCross (C - A) (w - A)) htEq
  rw [AffineMap.lineMap_apply] at heq
  simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right,
    Complex.real_smul, kwComplexCross_mul_real_right,
    kwComplexCross_self, mul_zero] at heq
  exact heq.symm



theorem kw_openSegments_disjoint_of_common_left_cross_ne
    {A B C : ℂ} (hcross : kwComplexCross (B - A) (C - A) ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ A z B} {z : ℂ | Sbtw ℝ A z C} := by
  rw [Set.disjoint_left]
  intro z hzAB hzAC
  obtain ⟨t, ht, htEq⟩ := hzAB.mem_image_Ioo
  obtain ⟨u, hu, huEq⟩ := hzAC.mem_image_Ioo
  have heq : AffineMap.lineMap A B t = AffineMap.lineMap A C u :=
    htEq.trans huEq.symm
  have hcrossEq := congrArg
    (fun w : ℂ ↦ kwComplexCross (B - A) (w - A)) heq
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply] at hcrossEq
  simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right,
    Complex.real_smul] at hcrossEq
  rw [kwComplexCross_mul_real_right, kwComplexCross_mul_real_right,
    kwComplexCross_self, mul_zero] at hcrossEq
  exact hcross (mul_eq_zero.mp hcrossEq.symm |>.resolve_left hu.1.ne')



theorem kw_fourVector_crossEar
    (p a b q : ℂ) (hb : b ≠ 0) (hq : q ≠ 0)
    (hsum : p + a + b + q = 0)
    (hbq : kwComplexCross b q ≠ 0)
    (hsign :
      (0 < kwComplexCross p a ∧ 0 < kwComplexCross a b ∧
          0 < kwComplexCross q p) ∨
        (kwComplexCross p a < 0 ∧ kwComplexCross a b < 0 ∧
          kwComplexCross q p < 0)) :
    kwComplexCross a b ≠ 0 ∧
      (Complex.arg q : Real.Angle) - (Complex.arg b : Real.Angle) ≠
        (Real.pi : Real.Angle) ∧
      ((0 < kwComplexCross p a ∧
          0 < kwComplexCross p (a + b)) ∨
        (kwComplexCross p a < 0 ∧
          kwComplexCross p (a + b) < 0)) ∧
      ((0 < kwComplexCross (a + b) b ∧
          0 < kwComplexCross (a + b) q) ∨
        (kwComplexCross (a + b) b < 0 ∧
          kwComplexCross (a + b) q < 0)) := by
  have hpdiag : kwComplexCross p (a + b) = kwComplexCross q p := by
    have hre := congrArg Complex.re hsum
    have him := congrArg Complex.im hsum
    simp only [Complex.add_re, Complex.zero_re] at hre
    simp only [Complex.add_im, Complex.zero_im] at him
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    linear_combination p.re * him - p.im * hre
  have hdiagb : kwComplexCross (a + b) b = kwComplexCross a b := by
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hdiagq : kwComplexCross (a + b) q = kwComplexCross q p := by
    have hre := congrArg Complex.re hsum
    have him := congrArg Complex.im hsum
    simp only [Complex.add_re, Complex.zero_re] at hre
    simp only [Complex.add_im, Complex.zero_im] at him
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    linear_combination q.im * hre - q.re * him
  constructor
  · rcases hsign with h | h <;> nlinarith [h.2.1]
  constructor
  · exact kw_angle_sub_ne_pi_of_cross_ne_zero hb hq hbq
  constructor
  · rw [hpdiag]
    rcases hsign with h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr ⟨h.1, h.2.2⟩
  · rw [hdiagb, hdiagq]
    rcases hsign with h | h
    · exact Or.inl ⟨h.2.1, h.2.2⟩
    · exact Or.inr ⟨h.2.1, h.2.2⟩


noncomputable def kwVectorTurnPhase (x y : ℂ) : ℂ :=
  kwAngleTurnPhase (Complex.arg x : Real.Angle)
    (Complex.arg y : Real.Angle)

theorem kwVectorTurnPhase_ne_zero (x y : ℂ) :
    kwVectorTurnPhase x y ≠ 0 := by
  unfold kwVectorTurnPhase kwAngleTurnPhase
  exact Complex.exp_ne_zero _


noncomputable def kwVectorPhasePath : List ℂ → ℂ
  | [] => 1
  | [_] => 1
  | x :: y :: tail =>
      kwVectorTurnPhase x y * kwVectorPhasePath (y :: tail)


noncomputable def kwVectorPhaseCycle : List ℂ → ℂ
  | [] => 1
  | x :: tail =>
      kwVectorPhasePath (x :: tail) *
        kwVectorTurnPhase ((x :: tail).getLastD x) x

@[simp] theorem kwVectorPhasePath_nil :
    kwVectorPhasePath [] = 1 := rfl

@[simp] theorem kwVectorPhasePath_singleton (x : ℂ) :
    kwVectorPhasePath [x] = 1 := rfl

@[simp] theorem kwVectorPhasePath_cons_cons
    (x y : ℂ) (tail : List ℂ) :
    kwVectorPhasePath (x :: y :: tail) =
      kwVectorTurnPhase x y * kwVectorPhasePath (y :: tail) := rfl

@[simp] theorem kwVectorPhaseCycle_nil :
    kwVectorPhaseCycle [] = 1 := rfl

@[simp] theorem kwVectorPhaseCycle_cons (x : ℂ) (tail : List ℂ) :
    kwVectorPhaseCycle (x :: tail) =
      kwVectorPhasePath (x :: tail) *
        kwVectorTurnPhase ((x :: tail).getLastD x) x := rfl



theorem kwVectorPhasePath_mul_last_eq_zipWith
    (x closing : ℂ) (tail : List ℂ) :
    kwVectorPhasePath (x :: tail) *
        kwVectorTurnPhase ((x :: tail).getLastD x) closing =
      (List.zipWith kwVectorTurnPhase (x :: tail)
        (tail ++ [closing])).prod := by
  induction tail generalizing x with
  | nil => simp [kwVectorPhasePath]
  | cons y tail ih =>
      simp only [kwVectorPhasePath_cons_cons, List.getLastD_cons,
        List.cons_append, List.zipWith_cons_cons, List.prod_cons]
      have hih := ih y
      simp only [List.getLastD_cons] at hih
      rw [← hih]
      ring



theorem kwVectorPhaseCycle_eq_zipWith (edges : List ℂ) :
    kwVectorPhaseCycle edges =
      (List.zipWith kwVectorTurnPhase edges (edges.rotate 1)).prod := by
  rcases edges with _ | ⟨x, tail⟩
  · simp
  · cases tail with
    | nil => simp [kwVectorPhaseCycle, kwVectorPhasePath,
        kwVectorTurnPhase]
    | cons y tail =>
        rw [kwVectorPhaseCycle_cons,
          kwVectorPhasePath_mul_last_eq_zipWith x x (y :: tail),
          List.zipWith_rotate_one]
        simp



theorem kwVectorPhaseCycle_rotate (edges : List ℂ) (r : ℕ) :
    kwVectorPhaseCycle (edges.rotate r) = kwVectorPhaseCycle edges := by
  rw [kwVectorPhaseCycle_eq_zipWith, kwVectorPhaseCycle_eq_zipWith]
  have hrotate :
      List.zipWith kwVectorTurnPhase (edges.rotate r)
          ((edges.rotate r).rotate 1) =
        (List.zipWith kwVectorTurnPhase edges (edges.rotate 1)).rotate r := by
    rw [List.zipWith_rotate_distrib kwVectorTurnPhase edges
      (edges.rotate 1) r (by simp)]
    congr 1
    simp only [List.rotate_rotate]
    rw [Nat.add_comm]
  rw [hrotate]
  exact (List.rotate_perm _ _).prod_eq



theorem kwVectorPhaseCycle_ofFn {n : ℕ} [NeZero n]
    (edge : Fin n → ℂ) :
    kwVectorPhaseCycle (List.ofFn edge) =
      kwLoopPhaseProduct kwVectorTurnPhase edge := by
  rw [kwVectorPhaseCycle_eq_zipWith]
  unfold kwLoopPhaseProduct
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hiLeft hiRight
    rw [List.getElem_zipWith]
    simp only [List.getElem_ofFn]
    rw [List.getElem_rotate]
    simp only [List.length_ofFn, List.getElem_ofFn]
    congr 2
    apply Fin.ext
    rw [Fin.val_add]
    simp [Nat.add_mod]



theorem KWStraightLineEmbedding.vectorTurnPhase_eq_turnPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart) :
    kwVectorTurnPhase
        (embedding.vertex dart.snd - embedding.vertex dart.fst)
        (embedding.vertex next.snd - embedding.vertex next.fst) =
      embedding.turnPhase dart next := by
  simpa only [kwVectorTurnPhase, kwAngleTurnPhase,
    kwPrincipalHalfAnglePhase] using
      embedding.principalPhase_eq_turnPhase dart next



theorem KWStraightLineEmbedding.vectorPhaseCycle_of_dartLoop
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwVectorPhaseCycle (List.ofFn fun k ↦
        embedding.vertex (loop k).snd - embedding.vertex (loop k).fst) =
      kwLoopPhaseProduct embedding.turnPhase loop := by
  rw [kwVectorPhaseCycle_ofFn]
  unfold kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k _
  exact embedding.vectorTurnPhase_eq_turnPhase (loop k) (loop (k + 1))




theorem KWStraightLineEmbedding.incident_collinear_sameRay
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart)
    (hadj : dart.snd = next.fst)
    (houter : dart.fst ≠ next.snd)
    (hcol : Collinear ℝ
      ({embedding.vertex dart.fst, embedding.vertex dart.snd,
        embedding.vertex next.snd} : Set ℂ)) :
    SameRay ℝ
      (embedding.vertex dart.snd - embedding.vertex dart.fst)
      (embedding.vertex next.snd - embedding.vertex next.fst) := by
  have hAB : dart.fst ≠ dart.snd := dart.fst_ne_snd
  have hBC : dart.snd ≠ next.snd := by
    rw [hadj]
    exact next.fst_ne_snd
  rcases hcol.wbtw_or_wbtw_or_wbtw with hmid | hmid | hmid
  · simpa only [vsub_eq_sub, hadj] using hmid.sameRay_vsub
  · have hstrict : Sbtw ℝ (embedding.vertex dart.snd)
        (embedding.vertex next.snd) (embedding.vertex dart.fst) :=
      ⟨hmid, embedding.vertex_injective.ne hBC.symm,
        embedding.vertex_injective.ne houter.symm⟩
    exact (embedding.vertex_not_strictly_between dart.symm next.snd
      hBC.symm houter.symm hstrict).elim
  · have hstrict : Sbtw ℝ (embedding.vertex next.snd)
        (embedding.vertex dart.fst) (embedding.vertex dart.snd) :=
      ⟨hmid, embedding.vertex_injective.ne houter,
        embedding.vertex_injective.ne hAB⟩
    exact (embedding.vertex_not_strictly_between next.symm dart.fst
      houter (by simpa only [hadj] using hAB) (by simpa only [hadj] using hstrict)).elim




structure KWFiniteSimplePolygon (n : ℕ) [NeZero n] where
  vertex : Fin n → ℂ
  three_le : 3 ≤ n
  vertex_injective : Function.Injective vertex
  vertex_not_strictly_between : ∀ (i j : Fin n),
    j ≠ i → j ≠ i + 1 →
      ¬Sbtw ℝ (vertex i) (vertex j) (vertex (i + 1))
  edgeInteriors_disjoint : ∀ (i j : Fin n), i ≠ j →
    Disjoint
      {z : ℂ | Sbtw ℝ (vertex i) z (vertex (i + 1))}
      {z : ℂ | Sbtw ℝ (vertex j) z (vertex (j + 1))}


def kwCyclicEdgeVector {n : ℕ} [NeZero n]
    (vertex : Fin n → ℂ) (i : Fin n) : ℂ :=
  vertex (i + 1) - vertex i


def kwCyclicEdgeList {n : ℕ} [NeZero n]
    (vertex : Fin n → ℂ) : List ℂ :=
  List.ofFn (kwCyclicEdgeVector vertex)



def kwRemoveVertexOne {n : ℕ} [NeZero n]
    (vertex : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun i ↦ vertex ((1 : Fin (n + 1)).succAbove i)

@[simp] theorem kwRemoveVertexOne_zero {n : ℕ} [NeZero n]
    (vertex : Fin (n + 1) → ℂ) :
    kwRemoveVertexOne vertex 0 = vertex 0 := by
  simp [kwRemoveVertexOne]

@[simp] theorem kwRemoveVertexOne_one {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (vertex : Fin (n + 1) → ℂ) :
    kwRemoveVertexOne vertex 1 = vertex 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [kwRemoveVertexOne]

@[simp] theorem kwRemoveVertexOne_succ_fixed
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) (i : Fin (m + 1)) :
    kwRemoveVertexOne vertex i.succ = vertex i.succ.succ := by
  simp [kwRemoveVertexOne]



theorem kwCyclicEdgeVector_removeVertexOne_zero
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (vertex : Fin (n + 1) → ℂ) :
    kwCyclicEdgeVector (kwRemoveVertexOne vertex) 0 =
      kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1 := by
  unfold kwCyclicEdgeVector
  have hnew : (0 : Fin n) + 1 = 1 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hold0 : (0 : Fin (n + 1)) + 1 = 1 := by
    apply Fin.ext
    simp
  have hold1 : (1 : Fin (n + 1)) + 1 = 2 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n + 1)]
  rw [hnew, hold0, hold1]
  rw [kwRemoveVertexOne_zero, kwRemoveVertexOne_one hn]
  ring



theorem kwCyclicEdgeVector_removeVertexOne_succ
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) (i : Fin (m + 1)) :
    kwCyclicEdgeVector (kwRemoveVertexOne vertex) i.succ =
      kwCyclicEdgeVector vertex i.succ.succ := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [kwCyclicEdgeVector, kwRemoveVertexOne]
    congr 1
  · simp [kwCyclicEdgeVector, kwRemoveVertexOne]
    have hlt : (1 : Fin (m + 3)) < (j.castSucc.succ + 1).succ := by
      change 1 < (j.castSucc.succ + 1).val + 1
      have hj := j.isLt
      have hnowrap : j.val + 2 < m + 2 := by omega
      simp [Fin.val_add, Nat.mod_eq_of_lt hnowrap]
    rw [Fin.succAbove_of_lt_succ _ _ hlt]
    congr 1
    apply Fin.ext
    have hj := j.isLt
    have hnew : (j.castSucc.succ).val + 1 < m + 2 := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hold : (j.castSucc.succ.succ).val + 1 < m + 3 := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    rw [Fin.val_succ, Fin.val_add_one_of_lt' hnew,
      Fin.val_add_one_of_lt' hold]
    simp

@[simp] theorem kwRemoveVertexOne_succ_add_one
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) (i : Fin (m + 1)) :
    kwRemoveVertexOne vertex (i.succ + 1) =
      vertex (i.succ.succ + 1) := by
  have hedge := kwCyclicEdgeVector_removeVertexOne_succ vertex i
  unfold kwCyclicEdgeVector at hedge
  rw [kwRemoveVertexOne_succ_fixed] at hedge
  linear_combination hedge



theorem kwCyclicEdgeList_removeVertexOne
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) :
    kwCyclicEdgeList (kwRemoveVertexOne vertex) =
      (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1) ::
        List.ofFn (fun i : Fin (m + 1) ↦
          kwCyclicEdgeVector vertex i.succ.succ) := by
  unfold kwCyclicEdgeList
  rw [List.ofFn_succ]
  congr 1
  · exact kwCyclicEdgeVector_removeVertexOne_zero (by omega) vertex
  · congr 1
    funext i
    exact kwCyclicEdgeVector_removeVertexOne_succ vertex i



theorem kwCyclicEdgeList_eq_first_two
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) :
    kwCyclicEdgeList vertex =
      kwCyclicEdgeVector vertex 0 :: kwCyclicEdgeVector vertex 1 ::
        List.ofFn (fun i : Fin (m + 1) ↦
          kwCyclicEdgeVector vertex i.succ.succ) := by
  unfold kwCyclicEdgeList
  rw [List.ofFn_succ, List.ofFn_succ]
  congr 2


def KWFiniteSimplePolygon.edgeVector {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n) (i : Fin n) : ℂ :=
  polygon.vertex (i + 1) - polygon.vertex i


def KWFiniteSimplePolygon.edgeList {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n) : List ℂ :=
  List.ofFn polygon.edgeVector


noncomputable def KWFiniteSimplePolygon.rotate
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (r : Fin n) :
    KWFiniteSimplePolygon n where
  vertex := fun i ↦ polygon.vertex (i + r)
  three_le := polygon.three_le
  vertex_injective := polygon.vertex_injective.comp
    (Equiv.addRight r).injective
  vertex_not_strictly_between := by
    intro i j hji hjsucc
    have hji' : j + r ≠ i + r := by
      intro h
      exact hji (add_right_cancel h)
    have hsucc (k : Fin n) : (k + 1) + r = (k + r) + 1 := by abel
    have hjsucc' : j + r ≠ (i + r) + 1 := by
      rw [← hsucc]
      intro h
      exact hjsucc (add_right_cancel h)
    change ¬Sbtw ℝ (polygon.vertex (i + r))
      (polygon.vertex (j + r)) (polygon.vertex (i + 1 + r))
    rw [hsucc]
    exact polygon.vertex_not_strictly_between (i + r) (j + r)
      hji' hjsucc'
  edgeInteriors_disjoint := by
    intro i j hij
    have hij' : i + r ≠ j + r := by
      intro h
      exact hij (add_right_cancel h)
    have hsucc (k : Fin n) : (k + 1) + r = (k + r) + 1 := by abel
    change Disjoint
      {z : ℂ | Sbtw ℝ (polygon.vertex (i + r)) z
        (polygon.vertex (i + 1 + r))}
      {z : ℂ | Sbtw ℝ (polygon.vertex (j + r)) z
        (polygon.vertex (j + 1 + r))}
    rw [hsucc i, hsucc j]
    exact polygon.edgeInteriors_disjoint (i + r) (j + r) hij'

@[simp] theorem KWFiniteSimplePolygon.edgeVector_eq_cyclic
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    polygon.edgeVector i = kwCyclicEdgeVector polygon.vertex i := rfl

@[simp] theorem KWFiniteSimplePolygon.edgeList_eq_cyclic
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    polygon.edgeList = kwCyclicEdgeList polygon.vertex := rfl

@[simp] theorem KWFiniteSimplePolygon.rotate_edgeVector
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (r i : Fin n) :
    (polygon.rotate r).edgeVector i = polygon.edgeVector (i + r) := by
  unfold KWFiniteSimplePolygon.edgeVector KWFiniteSimplePolygon.rotate
  dsimp only
  congr 2
  abel



theorem KWFiniteSimplePolygon.rotate_not_collinear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (r : Fin n) :
    ∀ i : Fin n, ¬Collinear ℝ
      ({(polygon.rotate r).vertex i,
        (polygon.rotate r).vertex (i + 1),
        (polygon.rotate r).vertex (i + 2)} : Set ℂ) := by
  intro i
  change ¬Collinear ℝ
    ({polygon.vertex (i + r), polygon.vertex (i + 1 + r),
      polygon.vertex (i + 2 + r)} : Set ℂ)
  have h1 : i + 1 + r = (i + r) + 1 := by abel
  have h2 : i + 2 + r = (i + r) + 2 := by abel
  rw [h1, h2]
  exact hnoncollinear (i + r)

theorem KWFiniteSimplePolygon.rotate_edgeList
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (r : Fin n) :
    (polygon.rotate r).edgeList = polygon.edgeList.rotate r.val := by
  change List.ofFn (polygon.rotate r).edgeVector =
    (List.ofFn polygon.edgeVector).rotate r.val
  apply List.ext_getElem
  · simp
  · intro i hiLeft hiRight
    rw [List.getElem_ofFn, List.getElem_rotate]
    simp only [List.length_ofFn, List.getElem_ofFn,
      KWFiniteSimplePolygon.rotate_edgeVector]
    congr 2

theorem KWFiniteSimplePolygon.edgeVector_ne_zero
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    polygon.edgeVector i ≠ 0 := by
  rw [KWFiniteSimplePolygon.edgeVector, sub_ne_zero]
  apply polygon.vertex_injective.ne
  intro hindex
  have hzeroOne : (0 : Fin n) = 1 := by
    apply add_left_cancel (a := i)
    simpa using hindex.symm
  have hval := congrArg Fin.val hzeroOne
  have hn : 3 ≤ n := polygon.three_le
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hval



theorem KWFiniteSimplePolygon.quadrilateral_edge_sum
    (polygon : KWFiniteSimplePolygon 4) (i : Fin 4) :
    polygon.edgeVector i + polygon.edgeVector (i + 1) +
        polygon.edgeVector (i + 2) + polygon.edgeVector (i + 3) = 0 := by
  have h11 : i + 1 + 1 = i + 2 := by abel
  have h21 : i + 2 + 1 = i + 3 := by abel
  have h31 : i + 3 + 1 = i := by
    rw [add_assoc]
    have h : (3 : Fin 4) + 1 = 0 := by decide
    rw [h, add_zero]
  simp only [KWFiniteSimplePolygon.edgeVector, h11, h21, h31]
  ring



theorem KWFiniteSimplePolygon.edge_cross_ne_zero_of_not_collinear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) (i : Fin n) :
    kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0 := by
  intro hzero
  apply hnoncollinear i
  apply kw_collinear_of_cross_sub_eq_zero
  have hidx : i + 1 + 1 = i + 2 := by
    rw [add_assoc]
    congr 1
    apply Fin.ext
    have hthree := polygon.three_le
    have hn : 2 < n := by omega
    simp [Fin.val_add, Nat.mod_eq_of_lt hn]
  simpa only [KWFiniteSimplePolygon.edgeVector, hidx] using hzero



theorem KWFiniteSimplePolygon.quadrilateral_not_cross_pattern_zero_two
    (polygon : KWFiniteSimplePolygon 4) :
    ¬(kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) *
          kwComplexCross (polygon.edgeVector 3) (polygon.edgeVector 0) < 0 ∧
      kwComplexCross (polygon.edgeVector 1) (polygon.edgeVector 2) *
          kwComplexCross (polygon.edgeVector 2) (polygon.edgeVector 3) < 0) := by
  rintro ⟨hAB, hCD⟩
  have he0 : polygon.edgeVector 0 =
      polygon.vertex 1 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he1 : polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 1 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he2 : polygon.edgeVector 2 =
      polygon.vertex 3 - polygon.vertex 2 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he3 : polygon.edgeVector 3 =
      polygon.vertex 0 - polygon.vertex 3 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  simp only [he0, he1, he2, he3] at hAB hCD
  have hcross := kw_exists_common_sbtw_of_cross_opposite
    (A := polygon.vertex 0) (B := polygon.vertex 1)
    (C := polygon.vertex 2) (D := polygon.vertex 3) (by
      convert hAB using 1 <;>
        unfold kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring) (by
      convert hCD using 1 <;>
        unfold kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring)
  obtain ⟨z, hz0, hz2⟩ := hcross
  exact Set.disjoint_left.mp
    (polygon.edgeInteriors_disjoint 0 2 (by decide)) hz0 hz2


theorem KWFiniteSimplePolygon.quadrilateral_not_cross_pattern_one_three
    (polygon : KWFiniteSimplePolygon 4) :
    ¬(kwComplexCross (polygon.edgeVector 1) (polygon.edgeVector 2) *
          kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) < 0 ∧
      kwComplexCross (polygon.edgeVector 2) (polygon.edgeVector 3) *
          kwComplexCross (polygon.edgeVector 3) (polygon.edgeVector 0) < 0) := by
  rintro ⟨hAB, hCD⟩
  have he0 : polygon.edgeVector 0 =
      polygon.vertex 1 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he1 : polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 1 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he2 : polygon.edgeVector 2 =
      polygon.vertex 3 - polygon.vertex 2 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he3 : polygon.edgeVector 3 =
      polygon.vertex 0 - polygon.vertex 3 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  simp only [he0, he1, he2, he3] at hAB hCD
  have hcross := kw_exists_common_sbtw_of_cross_opposite
    (A := polygon.vertex 1) (B := polygon.vertex 2)
    (C := polygon.vertex 3) (D := polygon.vertex 0) (by
      convert hAB using 1 <;>
        unfold kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring) (by
      convert hCD using 1 <;>
        unfold kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring)
  obtain ⟨z, hz1, hz3⟩ := hcross
  exact Set.disjoint_left.mp
    (polygon.edgeInteriors_disjoint 1 3 (by decide)) hz1 hz3

theorem KWFiniteSimplePolygon.add_one_ne_self
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    i + 1 ≠ i := by
  intro h
  have h10 : (1 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa using h
  have hval := congrArg Fin.val h10
  have hthree := polygon.three_le
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hval

theorem KWFiniteSimplePolygon.add_two_ne_self
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    i + 2 ≠ i := by
  intro h
  have h20 : (2 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa using h
  have hval := congrArg Fin.val h20
  have hthree := polygon.three_le
  simp [Nat.mod_eq_of_lt (by omega : 2 < n)] at hval

theorem KWFiniteSimplePolygon.add_two_ne_add_one
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    i + 2 ≠ i + 1 := by
  intro h
  have h21 : (2 : Fin n) = 1 := by
    apply add_left_cancel (a := i)
    simpa using h
  have hval := congrArg Fin.val h21
  have hthree := polygon.three_le
  have h1 : 1 < n := by omega
  have h2 : 2 < n := by omega
  simp [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval



theorem KWFiniteSimplePolygon.consecutive_wbtw_of_collinear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n)
    (hcol : Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    Wbtw ℝ (polygon.vertex i) (polygon.vertex (i + 1))
      (polygon.vertex (i + 2)) := by
  have hi1 := polygon.add_one_ne_self i
  have hi2 := polygon.add_two_ne_self i
  have h21 := polygon.add_two_ne_add_one i
  have h01 : polygon.vertex i ≠ polygon.vertex (i + 1) :=
    polygon.vertex_injective.ne hi1.symm
  have h02 : polygon.vertex i ≠ polygon.vertex (i + 2) :=
    polygon.vertex_injective.ne hi2.symm
  have h12 : polygon.vertex (i + 1) ≠ polygon.vertex (i + 2) :=
    polygon.vertex_injective.ne h21.symm
  rcases hcol.wbtw_or_wbtw_or_wbtw with hmid | hmid | hmid
  · exact hmid
  · exfalso
    have hstrict : Sbtw ℝ (polygon.vertex i)
        (polygon.vertex (i + 2)) (polygon.vertex (i + 1)) :=
      ⟨hmid.symm, h02.symm, h12.symm⟩
    exact polygon.vertex_not_strictly_between i (i + 2)
      hi2 h21 (by simpa using hstrict)
  · exfalso
    have hstrict : Sbtw ℝ (polygon.vertex (i + 1))
        (polygon.vertex i) (polygon.vertex (i + 2)) :=
      ⟨hmid.symm, h01, h02⟩
    exact polygon.vertex_not_strictly_between (i + 1) i
      hi1.symm (by
        have hidx : i + 1 + 1 = i + 2 := by
          rw [add_assoc]
          congr 1
          apply Fin.ext
          have hthree := polygon.three_le
          have hn : 2 < n := by omega
          simp [Fin.val_add, Nat.mod_eq_of_lt hn]
        rw [hidx]
        exact hi2.symm)
      (by
        have hidx : i + 1 + 1 = i + 2 := by
          rw [add_assoc]
          congr 1
          apply Fin.ext
          have hthree := polygon.three_le
          have hn : 2 < n := by omega
          simp [Fin.val_add, Nat.mod_eq_of_lt hn]
        simpa only [hidx] using hstrict)



theorem KWFiniteSimplePolygon.not_sbtw_zero_two_of_between
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1)
      (polygon.vertex 2))
    (k : Fin n) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk2 : k ≠ 2) :
    ¬Sbtw ℝ (polygon.vertex 0) (polygon.vertex k) (polygon.vertex 2) := by
  intro hk
  have h01idx : (0 : Fin n) + 1 = 1 := by
    apply Fin.ext
    have hthree := polygon.three_le
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h12idx : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    have hthree := polygon.three_le
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n)]
  have h02 : polygon.vertex 0 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_two_ne_self 0).symm)
  have h01 : polygon.vertex 0 ≠ polygon.vertex 1 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_one_ne_self 0).symm)
  have h12 : polygon.vertex 1 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_two_ne_add_one 0).symm)
  rcases kw_sbtw_eq_or_sbtw_or_sbtw h02 h01 h12 hbetween hk with
      heq | hk01 | hk12
  · exact hk1 (polygon.vertex_injective heq)
  · exact polygon.vertex_not_strictly_between 0 k
      hk0 (by simpa only [h01idx] using hk1)
      (by simpa only [h01idx] using hk01)
  · exact polygon.vertex_not_strictly_between 1 k
      hk1 (by simpa only [h12idx] using hk2)
      (by simpa only [h12idx] using hk12)



theorem KWFiniteSimplePolygon.diagonal_zero_two_disjoint
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1)
      (polygon.vertex 2))
    (k : Fin n) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    Disjoint
      {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)}
      {z : ℂ | Sbtw ℝ (polygon.vertex k) z (polygon.vertex (k + 1))} := by
  rw [Set.disjoint_left]
  intro z hzdiag hzk
  have h01idx : (0 : Fin n) + 1 = 1 := by
    apply Fin.ext
    have hthree := polygon.three_le
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h12idx : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    have hthree := polygon.three_le
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n)]
  have h02 : polygon.vertex 0 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_two_ne_self 0).symm)
  have h01 : polygon.vertex 0 ≠ polygon.vertex 1 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_one_ne_self 0).symm)
  have h12 : polygon.vertex 1 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_two_ne_add_one 0).symm)
  rcases kw_sbtw_eq_or_sbtw_or_sbtw h02 h01 h12 hbetween hzdiag with
      rfl | hz01 | hz12
  · have hkSucc : (1 : Fin n) ≠ k + 1 := by
      intro h
      apply hk0
      apply add_right_cancel (b := (1 : Fin n))
      simpa using h.symm
    exact polygon.vertex_not_strictly_between k 1 hk1.symm hkSucc hzk
  · exact (Set.disjoint_left.mp
      (polygon.edgeInteriors_disjoint 0 k hk0.symm))
        (by simpa only [h01idx] using hz01) hzk
  · exact (Set.disjoint_left.mp
      (polygon.edgeInteriors_disjoint 1 k hk1.symm))
        (by simpa only [h12idx] using hz12) hzk



def KWFiniteSimplePolygon.VertexOneRemovalIsSimple
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  (∀ (i j : Fin (m + 2)), j ≠ i → j ≠ i + 1 →
      ¬Sbtw ℝ (kwRemoveVertexOne polygon.vertex i)
        (kwRemoveVertexOne polygon.vertex j)
        (kwRemoveVertexOne polygon.vertex (i + 1))) ∧
    ∀ (i j : Fin (m + 2)), i ≠ j →
      Disjoint
        {z : ℂ | Sbtw ℝ (kwRemoveVertexOne polygon.vertex i) z
          (kwRemoveVertexOne polygon.vertex (i + 1))}
        {z : ℂ | Sbtw ℝ (kwRemoveVertexOne polygon.vertex j) z
          (kwRemoveVertexOne polygon.vertex (j + 1))}




def KWFiniteSimplePolygon.VertexOneDiagonalIsClean
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  (∀ k : Fin (m + 3), k ≠ 0 → k ≠ 1 → k ≠ 2 →
      ¬Sbtw ℝ (polygon.vertex 0) (polygon.vertex k) (polygon.vertex 2)) ∧
    ∀ k : Fin (m + 3), k ≠ 0 → k ≠ 1 →
      Disjoint
        {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)}
        {z : ℂ | Sbtw ℝ (polygon.vertex k) z
          (polygon.vertex (k + 1))}



theorem KWFiniteSimplePolygon.vertexOneRemovalIsSimple_of_diagonalIsClean
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3))
    (hclean : polygon.VertexOneDiagonalIsClean) :
    polygon.VertexOneRemovalIsSimple := by
  let f : Fin (m + 2) → Fin (m + 3) :=
    (1 : Fin (m + 3)).succAbove
  have hfInjective : Function.Injective f :=
    Fin.succAbove_right_injective
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 2 := by simp [f]
  constructor
  · intro i j hji hjsucc
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (hji rfl).elim
        | succ s =>
            have hk0 : f s.succ ≠ 0 := by
              rw [← hf0]
              exact hfInjective.ne (by simp)
            have hk1 : f s.succ ≠ 1 :=
              Fin.succAbove_ne (1 : Fin (m + 3)) s.succ
            have hk2 : f s.succ ≠ 2 := by
              rw [← hf1]
              exact hfInjective.ne hjsucc
            simpa only [kwRemoveVertexOne, f] using
              hclean.1 (f s.succ) hk0 hk1 hk2
    | succ q =>
        let old : Fin (m + 3) := f q.succ
        have hendVertex : polygon.vertex (f (q.succ + 1)) =
            polygon.vertex (old + 1) := by
          simpa only [f, old, kwRemoveVertexOne] using
            kwRemoveVertexOne_succ_add_one polygon.vertex q
        have hend : f (q.succ + 1) = old + 1 :=
          polygon.vertex_injective hendVertex
        have hjOld : f j ≠ old := hfInjective.ne hji
        have hjEnd : f j ≠ old + 1 := by
          rw [← hend]
          exact hfInjective.ne hjsucc
        change ¬Sbtw ℝ (polygon.vertex (f q.succ))
          (polygon.vertex (f j)) (polygon.vertex (f (q.succ + 1)))
        rw [hend]
        exact polygon.vertex_not_strictly_between old (f j) hjOld hjEnd
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ qj =>
            have hk0 : f qj.succ ≠ 0 := by
              rw [← hf0]
              exact hfInjective.ne (by simp)
            have hk1 : f qj.succ ≠ 1 :=
              Fin.succAbove_ne (1 : Fin (m + 3)) qj.succ
            change Disjoint
              {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)}
              {z : ℂ | Sbtw ℝ (polygon.vertex (f qj.succ)) z
                (polygon.vertex (f (qj.succ + 1)))}
            have hendVertex : polygon.vertex (f (qj.succ + 1)) =
                polygon.vertex (f qj.succ + 1) := by
              simpa only [f, kwRemoveVertexOne] using
                kwRemoveVertexOne_succ_add_one polygon.vertex qj
            rw [hendVertex]
            exact hclean.2 (f qj.succ) hk0 hk1
    | succ qi =>
        cases j using Fin.cases with
        | zero =>
            have hk0 : f qi.succ ≠ 0 := by
              rw [← hf0]
              exact hfInjective.ne (by simp)
            have hk1 : f qi.succ ≠ 1 :=
              Fin.succAbove_ne (1 : Fin (m + 3)) qi.succ
            have hendVertex : polygon.vertex (f (qi.succ + 1)) =
                polygon.vertex (f qi.succ + 1) := by
              simpa only [f, kwRemoveVertexOne] using
                kwRemoveVertexOne_succ_add_one polygon.vertex qi
            change Disjoint
              {z : ℂ | Sbtw ℝ (polygon.vertex (f qi.succ)) z
                (polygon.vertex (f (qi.succ + 1)))}
              {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)}
            rw [hendVertex]
            exact (hclean.2 (f qi.succ) hk0 hk1).symm
        | succ qj =>
            have holdNe : f qi.succ ≠ f qj.succ := hfInjective.ne hij
            have hiEndVertex : polygon.vertex (f (qi.succ + 1)) =
                polygon.vertex (f qi.succ + 1) := by
              simpa only [f, kwRemoveVertexOne] using
                kwRemoveVertexOne_succ_add_one polygon.vertex qi
            have hjEndVertex : polygon.vertex (f (qj.succ + 1)) =
                polygon.vertex (f qj.succ + 1) := by
              simpa only [f, kwRemoveVertexOne] using
                kwRemoveVertexOne_succ_add_one polygon.vertex qj
            change Disjoint
              {z : ℂ | Sbtw ℝ (polygon.vertex (f qi.succ)) z
                (polygon.vertex (f (qi.succ + 1)))}
              {z : ℂ | Sbtw ℝ (polygon.vertex (f qj.succ)) z
                (polygon.vertex (f (qj.succ + 1)))}
            rw [hiEndVertex, hjEndVertex]
            exact polygon.edgeInteriors_disjoint (f qi.succ) (f qj.succ)
              holdNe





theorem KWFiniteSimplePolygon.outerTurns_ne_pi_of_diagonalIsClean
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hclean : polygon.VertexOneDiagonalIsClean) :
    (Complex.arg (polygon.edgeVector 0 + polygon.edgeVector 1) :
          Real.Angle) -
        (Complex.arg (polygon.edgeVector (-1)) : Real.Angle) ≠
          (Real.pi : Real.Angle) ∧
      (Complex.arg (polygon.edgeVector 2) : Real.Angle) -
        (Complex.arg (polygon.edgeVector 0 + polygon.edgeVector 1) :
          Real.Angle) ≠ (Real.pi : Real.Angle) := by
  have hn : 4 ≤ m + 3 := by omega
  have hprevSucc : (-1 : Fin (m + 3)) + 1 = 0 := by abel
  have h01 : (0 : Fin (m + 3)) + 1 = 1 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
  have h12 : (1 : Fin (m + 3)) + 1 = 2 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have h23 : (2 : Fin (m + 3)) + 1 = 3 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have hprev0 : (-1 : Fin (m + 3)) ≠ 0 := by
    intro h
    have heq := congrArg (fun k : Fin (m + 3) ↦ k + 1) h
    have h10 : (1 : Fin (m + 3)) ≠ 0 := by
      simpa only [h01] using polygon.add_one_ne_self 0
    exact h10 (by simpa only [hprevSucc, zero_add] using heq.symm)
  have h30 : (3 : Fin (m + 3)) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hval
  have h31 : (3 : Fin (m + 3)) ≠ 1 := by
    intro h
    have hval := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 1 < m + 3)] at hval
  have h32 : (3 : Fin (m + 3)) ≠ 2 := by
    intro h
    have hval := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hval
  have h02 : (0 : Fin (m + 3)) ≠ 2 := by
    exact (polygon.add_two_ne_self 0).symm
  have h03 : (0 : Fin (m + 3)) ≠ 3 := h30.symm
  have h20 : (2 : Fin (m + 3)) ≠ 0 := h02.symm
  have hprev1 : (-1 : Fin (m + 3)) ≠ 1 := by
    intro h
    have heq := congrArg (fun k : Fin (m + 3) ↦ k + 1) h
    exact h20 (by simpa only [hprevSucc, h12] using heq.symm)
  have hprev2 : (-1 : Fin (m + 3)) ≠ 2 := by
    intro h
    have heq := congrArg (fun k : Fin (m + 3) ↦ k + 1) h
    exact h30 (by simpa only [hprevSucc, h23] using heq.symm)
  have h2prev : (2 : Fin (m + 3)) ≠ -1 := hprev2.symm
  have h2prevSucc : (2 : Fin (m + 3)) ≠ (-1) + 1 := by
    simpa only [hprevSucc] using h20
  have h0three : (0 : Fin (m + 3)) ≠ 2 + 1 := by
    simpa only [h23] using h03
  have hleft := kw_angle_diagonal_ne_pi_of_no_between
    (polygon.vertex_injective.ne hprev0)
    (polygon.vertex_injective.ne h02)
    (polygon.vertex_injective.ne hprev2)
    (hclean.1 (-1) hprev0 hprev1 hprev2)
    (by
      simpa only [hprevSucc] using
        polygon.vertex_not_strictly_between (-1) 2 h2prev h2prevSucc)
  have hright := kw_angle_diagonal_ne_pi_of_no_between
    (polygon.vertex_injective.ne h02)
    (polygon.vertex_injective.ne h32.symm)
    (polygon.vertex_injective.ne h03)
    (by
      simpa only [h23] using
        polygon.vertex_not_strictly_between 2 0 h02 h0three)
    (hclean.1 3 h30 h31 h32)
  have heprev : polygon.edgeVector (-1) =
      polygon.vertex 0 - polygon.vertex (-1) := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [hprevSucc]
  have he0 : polygon.edgeVector 0 =
      polygon.vertex 1 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [h01]
  have he1 : polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 1 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [h12]
  have he2 : polygon.edgeVector 2 =
      polygon.vertex 3 - polygon.vertex 2 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [h23]
  have hdiag : polygon.edgeVector 0 + polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 0 := by
    rw [he0, he1]
    ring
  rw [heprev, he2, hdiag]
  exact ⟨hleft, hright⟩


theorem KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_between
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3))
    (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1)
      (polygon.vertex 2)) :
    polygon.VertexOneDiagonalIsClean := by
  constructor
  · exact polygon.not_sbtw_zero_two_of_between hbetween
  · exact polygon.diagonal_zero_two_disjoint hbetween



theorem KWFiniteSimplePolygon.vertexOneRemovalIsSimple_of_between
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3))
    (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1)
      (polygon.vertex 2)) :
    polygon.VertexOneRemovalIsSimple := by
  exact polygon.vertexOneRemovalIsSimple_of_diagonalIsClean
    (polygon.vertexOneDiagonalIsClean_of_between hbetween)



noncomputable def KWStraightLineEmbedding.cyclePolygon
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    KWFiniteSimplePolygon p.darts.length := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let loop := kwGraphCycleDartLoop p
  have hvalid := kwGraphCycleDartLoop_valid p hp
  have hedgeNodup :
      (List.ofFn fun i : Fin p.darts.length ↦ (loop i).edge).Nodup := by
    rw [List.ofFn_comp', kwGraphCycleDartLoop_ofFn]
    simpa [SimpleGraph.Walk.edges] using hp.edges_nodup
  have hedgeInj : Function.Injective
      (fun i : Fin p.darts.length ↦ (loop i).edge) :=
    List.nodup_ofFn.mp hedgeNodup
  have hloopFst : ∀ i : Fin p.darts.length,
      (loop i).fst = p.getVert i.val := by
    intro i
    exact congrArg (fun dart : G.Dart ↦ dart.fst)
      (SimpleGraph.Walk.darts_getElem_eq_getVert i.val i.isLt)
  have hloopFstInj : Function.Injective
      (fun i : Fin p.darts.length ↦ (loop i).fst) := by
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn'
    · simp only [Set.mem_setOf_eq]
      rw [← SimpleGraph.Walk.length_darts]
      exact Nat.le_sub_one_of_lt i.isLt
    · simp only [Set.mem_setOf_eq]
      rw [← SimpleGraph.Walk.length_darts]
      exact Nat.le_sub_one_of_lt j.isLt
    · simpa only [hloopFst i, hloopFst j] using hij
  refine
    { vertex := fun i ↦ embedding.vertex (loop i).fst
      three_le := by
        rw [SimpleGraph.Walk.length_darts]
        exact hp.three_le_length
      vertex_injective := ?_
      vertex_not_strictly_between := ?_
      edgeInteriors_disjoint := ?_ }
  · intro i j hij
    exact hloopFstInj (embedding.vertex_injective hij)
  · intro i j hji hjsucc
    have hjfst : (loop j).fst ≠ (loop i).fst :=
      hloopFstInj.ne hji
    have hjsnd : (loop j).fst ≠ (loop i).snd := by
      rw [hvalid i]
      exact hloopFstInj.ne hjsucc
    change ¬Sbtw ℝ (embedding.vertex (loop i).fst)
      (embedding.vertex (loop j).fst) (embedding.vertex (loop (i + 1)).fst)
    rw [← hvalid i]
    exact embedding.vertex_not_strictly_between (loop i) (loop j).fst
      hjfst hjsnd
  · intro i j hij
    change Disjoint
      {z : ℂ | Sbtw ℝ (embedding.vertex (loop i).fst) z
        (embedding.vertex (loop (i + 1)).fst)}
      {z : ℂ | Sbtw ℝ (embedding.vertex (loop j).fst) z
        (embedding.vertex (loop (j + 1)).fst)}
    rw [← hvalid i, ← hvalid j]
    exact embedding.edgeInteriors_disjoint (loop i) (loop j)
      (fun hedge ↦ hij (hedgeInj hedge))



theorem KWStraightLineEmbedding.cyclePolygon_edgeList
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (embedding.cyclePolygon p hp).edgeList =
      List.ofFn fun k : Fin p.darts.length ↦
        embedding.vertex (kwGraphCycleDartLoop p k).snd -
          embedding.vertex (kwGraphCycleDartLoop p k).fst := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  unfold KWFiniteSimplePolygon.edgeList
  congr 1
  funext k
  unfold KWFiniteSimplePolygon.edgeVector
  dsimp only [KWStraightLineEmbedding.cyclePolygon]
  change embedding.vertex (kwGraphCycleDartLoop p (k + 1)).fst -
      embedding.vertex (kwGraphCycleDartLoop p k).fst = _
  rw [← kwGraphCycleDartLoop_valid p hp k]


theorem KWFiniteSimplePolygon.not_collinear_three
    (polygon : KWFiniteSimplePolygon 3) :
    ¬Collinear ℝ
      ({polygon.vertex 0, polygon.vertex 1, polygon.vertex 2} : Set ℂ) := by
  intro hcol
  have h01 : polygon.vertex 0 ≠ polygon.vertex 1 :=
    polygon.vertex_injective.ne (by decide)
  have h12 : polygon.vertex 1 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by decide)
  have h20 : polygon.vertex 2 ≠ polygon.vertex 0 :=
    polygon.vertex_injective.ne (by decide)
  rcases hcol.wbtw_or_wbtw_or_wbtw with hmid | hmid | hmid
  · have hstrict : Sbtw ℝ (polygon.vertex 2)
        (polygon.vertex 1) (polygon.vertex 0) :=
      ⟨hmid.symm, h12, h01.symm⟩
    exact polygon.vertex_not_strictly_between 2 1
      (by decide) (by decide) (by simpa using hstrict)
  · have hstrict : Sbtw ℝ (polygon.vertex 0)
        (polygon.vertex 2) (polygon.vertex 1) :=
      ⟨hmid.symm, h20, h12.symm⟩
    exact polygon.vertex_not_strictly_between 0 2
      (by decide) (by decide) (by simpa using hstrict)
  · have hstrict : Sbtw ℝ (polygon.vertex 1)
        (polygon.vertex 0) (polygon.vertex 2) :=
      ⟨hmid.symm, h01, h20.symm⟩
    exact polygon.vertex_not_strictly_between 1 0
      (by decide) (by decide) (by simpa using hstrict)


theorem kwVectorPhasePath_cons_congr {x : ℂ} {left right : List ℂ}
    (h : kwVectorPhasePath left = kwVectorPhasePath right)
    (hleft : left ≠ []) (hright : right ≠ [])
    (hhead : left.head hleft = right.head hright) :
    kwVectorPhasePath (x :: left) = kwVectorPhasePath (x :: right) := by
  obtain ⟨y, leftTail, rfl⟩ := List.exists_cons_of_ne_nil hleft
  obtain ⟨z, rightTail, rfl⟩ := List.exists_cons_of_ne_nil hright
  simp only [List.head_cons] at hhead
  subst z
  simp only [kwVectorPhasePath_cons_cons]
  rw [h]



theorem kwVectorTurnPhase_ear_splice
    (previous incoming outgoing next : ℂ)
    (hp : previous ≠ 0) (hi : incoming ≠ 0)
    (ho : outgoing ≠ 0) (hn : next ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hrightTurn :
      (Complex.arg next : Real.Angle) -
        (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
    (hleft :
      (0 < kwComplexCross previous incoming ∧
          0 < kwComplexCross previous (incoming + outgoing)) ∨
        (kwComplexCross previous incoming < 0 ∧
          kwComplexCross previous (incoming + outgoing) < 0))
    (hright :
      (0 < kwComplexCross (incoming + outgoing) outgoing ∧
          0 < kwComplexCross (incoming + outgoing) next) ∨
        (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
          kwComplexCross (incoming + outgoing) next < 0)) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  exact kwAngleTurnPhase_ear_splice_vectors previous incoming outgoing next
    hp hi ho hn hmiddle hrightTurn hleft hright



theorem kwVectorTurnPhase_straight_splice
    (previous incoming outgoing next : ℂ)
    (houtgoing :
      (Complex.arg outgoing : Real.Angle) =
        (Complex.arg incoming : Real.Angle))
    (hdiagonal :
      (Complex.arg (incoming + outgoing) : Real.Angle) =
        (Complex.arg incoming : Real.Angle)) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  simp only [kwVectorTurnPhase, houtgoing, hdiagonal]
  simp [kwAngleTurnPhase]



theorem kwVectorTurnPhase_straight_splice_of_sameRay
    (previous incoming outgoing next : ℂ)
    (hi : incoming ≠ 0) (ho : outgoing ≠ 0)
    (hsame : SameRay ℝ incoming outgoing) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  have houtgoing : outgoing.arg = incoming.arg := by
    rcases Complex.sameRay_iff.mp hsame with hzero | hzero | harg
    · exact (hi hzero).elim
    · exact (ho hzero).elim
    · exact harg.symm
  have hsum : incoming + outgoing ≠ 0 := by
    intro hzero
    have hnorm := hsame.norm_add
    rw [hzero, norm_zero] at hnorm
    have hiNorm : 0 < ‖incoming‖ := norm_pos_iff.mpr hi
    have hoNorm : 0 < ‖outgoing‖ := norm_pos_iff.mpr ho
    nlinarith
  have hsumRay : SameRay ℝ (incoming + outgoing) incoming :=
    SameRay.rfl.add_left hsame.symm
  have hdiagonal : (incoming + outgoing).arg = incoming.arg := by
    rcases Complex.sameRay_iff.mp hsumRay with hzero | hzero | harg
    · exact (hsum hzero).elim
    · exact (hi hzero).elim
    · exact harg
  exact kwVectorTurnPhase_straight_splice previous incoming outgoing next
    (congrArg (fun r : ℝ ↦ (r : Real.Angle)) houtgoing)
    (congrArg (fun r : ℝ ↦ (r : Real.Angle)) hdiagonal)



theorem KWFiniteSimplePolygon.straight_local_phase
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n)
    (hbetween : Wbtw ℝ (polygon.vertex i)
      (polygon.vertex (i + 1)) (polygon.vertex (i + 2))) :
    kwVectorTurnPhase (polygon.edgeVector (i - 1))
          (polygon.edgeVector i) *
        kwVectorTurnPhase (polygon.edgeVector i)
          (polygon.edgeVector (i + 1)) *
        kwVectorTurnPhase (polygon.edgeVector (i + 1))
          (polygon.edgeVector (i + 2)) =
      kwVectorTurnPhase (polygon.edgeVector (i - 1))
          (polygon.edgeVector i + polygon.edgeVector (i + 1)) *
        kwVectorTurnPhase
          (polygon.edgeVector i + polygon.edgeVector (i + 1))
          (polygon.edgeVector (i + 2)) := by
  apply kwVectorTurnPhase_straight_splice_of_sameRay
  · exact polygon.edgeVector_ne_zero i
  · exact polygon.edgeVector_ne_zero (i + 1)
  · unfold KWFiniteSimplePolygon.edgeVector
    have hidx : i + 1 + 1 = i + 2 := by
      rw [add_assoc]
      congr 1
      apply Fin.ext
      have hthree := polygon.three_le
      have hn : 2 < n := by omega
      simp [Fin.val_add, Nat.mod_eq_of_lt hn]
    rw [hidx]
    exact hbetween.sameRay_vsub




theorem KWFiniteSimplePolygon.collinear_local_phase
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n)
    (hcol : Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    kwVectorTurnPhase (polygon.edgeVector (i - 1))
          (polygon.edgeVector i) *
        kwVectorTurnPhase (polygon.edgeVector i)
          (polygon.edgeVector (i + 1)) *
        kwVectorTurnPhase (polygon.edgeVector (i + 1))
          (polygon.edgeVector (i + 2)) =
      kwVectorTurnPhase (polygon.edgeVector (i - 1))
          (polygon.edgeVector i + polygon.edgeVector (i + 1)) *
        kwVectorTurnPhase
          (polygon.edgeVector i + polygon.edgeVector (i + 1))
          (polygon.edgeVector (i + 2)) :=
  polygon.straight_local_phase i
    (polygon.consecutive_wbtw_of_collinear i hcol)



noncomputable def KWFiniteSimplePolygon.removeVertexOne
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple) :
    KWFiniteSimplePolygon (m + 2) where
  vertex := kwRemoveVertexOne polygon.vertex
  three_le := by omega
  vertex_injective := polygon.vertex_injective.comp
    (Fin.succAbove_right_injective (p := (1 : Fin (m + 3))))
  vertex_not_strictly_between := hsimple.1
  edgeInteriors_disjoint := hsimple.2

@[simp] theorem KWFiniteSimplePolygon.removeVertexOne_vertex
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple) :
    (polygon.removeVertexOne hm hsimple).vertex =
      kwRemoveVertexOne polygon.vertex := rfl

theorem KWFiniteSimplePolygon.removeVertexOne_edgeList
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple) :
    (polygon.removeVertexOne hm hsimple).edgeList =
      (polygon.edgeVector 0 + polygon.edgeVector 1) ::
        List.ofFn (fun i : Fin (m + 1) ↦ polygon.edgeVector i.succ.succ) := by
  rw [KWFiniteSimplePolygon.edgeList_eq_cyclic]
  change kwCyclicEdgeList (kwRemoveVertexOne polygon.vertex) = _
  simpa only [KWFiniteSimplePolygon.edgeVector_eq_cyclic] using
    kwCyclicEdgeList_removeVertexOne polygon.vertex



def KWFiniteSimplePolygon.VertexOnePhaseEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  let remaining := List.ofFn (fun i : Fin (m + 1) ↦
    polygon.edgeVector i.succ.succ)
  kwVectorTurnPhase (remaining.tail.getLast (by
        simp [remaining]; omega)) (polygon.edgeVector 0) *
      kwVectorTurnPhase (polygon.edgeVector 0) (polygon.edgeVector 1) *
      kwVectorTurnPhase (polygon.edgeVector 1)
        (remaining.head (by simp [remaining])) =
    kwVectorTurnPhase (remaining.tail.getLast (by
        simp [remaining]; omega))
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
      kwVectorTurnPhase
        (polygon.edgeVector 0 + polygon.edgeVector 1)
        (remaining.head (by simp [remaining]))




def KWFiniteSimplePolygon.VertexOneCrossEar
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) ≠ 0 ∧
    (Complex.arg (polygon.edgeVector 2) : Real.Angle) -
        (Complex.arg (polygon.edgeVector 1) : Real.Angle) ≠
      (Real.pi : Real.Angle) ∧
    ((0 < kwComplexCross (polygon.edgeVector (-1))
          (polygon.edgeVector 0) ∧
        0 < kwComplexCross (polygon.edgeVector (-1))
          (polygon.edgeVector 0 + polygon.edgeVector 1)) ∨
      (kwComplexCross (polygon.edgeVector (-1))
            (polygon.edgeVector 0) < 0 ∧
        kwComplexCross (polygon.edgeVector (-1))
            (polygon.edgeVector 0 + polygon.edgeVector 1) < 0)) ∧
    ((0 < kwComplexCross
          (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 1) ∧
        0 < kwComplexCross
          (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2)) ∨
      (kwComplexCross
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 1) < 0 ∧
        kwComplexCross
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 2) < 0))



def KWFiniteSimplePolygon.VertexOneGeometricEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  polygon.VertexOneDiagonalIsClean ∧ polygon.VertexOnePhaseEar hm





def KWFiniteSimplePolygon.VertexOneAlignedSideEar
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  polygon.VertexOneDiagonalIsClean ∧
    kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) ≠ 0 ∧
    ((0 < kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) ∧
          0 < kwComplexCross (polygon.edgeVector (-1))
            (polygon.edgeVector 0 + polygon.edgeVector 1)) ∨
      (kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) < 0 ∧
          kwComplexCross (polygon.edgeVector (-1))
            (polygon.edgeVector 0 + polygon.edgeVector 1) < 0)) ∧
    ((0 < kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) ∧
          0 < kwComplexCross
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 2)) ∨
      (kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) < 0 ∧
          kwComplexCross
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 2) < 0))




def kwAngleTurnWrap (a b c : Real.Angle) : Prop :=
  b - a ≠ (Real.pi : Real.Angle) ∧
    c - b ≠ (Real.pi : Real.Angle) ∧
    c - a ≠ (Real.pi : Real.Angle) ∧
    (b - a).sign = (c - b).sign ∧
    (b - a).sign ≠ (c - a).sign




def kwAngleTurnNoWrap (a b c : Real.Angle) : Prop :=
  b - a ≠ (Real.pi : Real.Angle) ∧
    c - b ≠ (Real.pi : Real.Angle) ∧
    ((b - a).sign ≠ (c - b).sign ∨
      (b - a).sign = (c - a).sign)



theorem kwAngleTurnNoWrap_or_wrap (a b c : Real.Angle)
    (hab : b - a ≠ (Real.pi : Real.Angle))
    (hbc : c - b ≠ (Real.pi : Real.Angle))
    (hac : c - a ≠ (Real.pi : Real.Angle)) :
    kwAngleTurnNoWrap a b c ∨ kwAngleTurnWrap a b c := by
  by_cases hsame : (b - a).sign = (c - b).sign
  · by_cases houter : (b - a).sign = (c - a).sign
    · exact Or.inl ⟨hab, hbc, Or.inr houter⟩
    · exact Or.inr ⟨hab, hbc, hac, hsame, houter⟩
  · exact Or.inl ⟨hab, hbc, Or.inl hsame⟩



def KWFiniteSimplePolygon.VertexOneDoubleWrapEar
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  let previous := polygon.edgeVector (-1)
  let incoming := polygon.edgeVector 0
  let outgoing := polygon.edgeVector 1
  let next := polygon.edgeVector 2
  let diagonal := incoming + outgoing
  polygon.VertexOneDiagonalIsClean ∧
    kwComplexCross incoming outgoing ≠ 0 ∧
    kwAngleTurnWrap (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg diagonal : Real.Angle) ∧
    kwAngleTurnWrap (Complex.arg diagonal : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)




def KWFiniteSimplePolygon.VertexOneStrictParityEar
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  let previous := polygon.edgeVector (-1)
  let incoming := polygon.edgeVector 0
  let outgoing := polygon.edgeVector 1
  let next := polygon.edgeVector 2
  let diagonal := incoming + outgoing
  polygon.VertexOneDiagonalIsClean ∧
    kwComplexCross incoming outgoing ≠ 0 ∧
    ((kwAngleTurnNoWrap (Complex.arg previous : Real.Angle)
          (Complex.arg incoming : Real.Angle)
          (Complex.arg diagonal : Real.Angle) ∧
        kwAngleTurnNoWrap (Complex.arg diagonal : Real.Angle)
          (Complex.arg outgoing : Real.Angle)
          (Complex.arg next : Real.Angle)) ∨
      (kwAngleTurnWrap (Complex.arg previous : Real.Angle)
          (Complex.arg incoming : Real.Angle)
          (Complex.arg diagonal : Real.Angle) ∧
        kwAngleTurnWrap (Complex.arg diagonal : Real.Angle)
          (Complex.arg outgoing : Real.Angle)
          (Complex.arg next : Real.Angle)))



theorem KWFiniteSimplePolygon.rotated_vertexOneCrossEar_of_sign
    (polygon : KWFiniteSimplePolygon 4)
    (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (i : Fin 4)
    (hsign :
      (0 < kwComplexCross (polygon.edgeVector (i + 3))
            (polygon.edgeVector i) ∧
        0 < kwComplexCross (polygon.edgeVector i)
            (polygon.edgeVector (i + 1)) ∧
        0 < kwComplexCross (polygon.edgeVector (i + 2))
            (polygon.edgeVector (i + 3))) ∨
      (kwComplexCross (polygon.edgeVector (i + 3))
              (polygon.edgeVector i) < 0 ∧
        kwComplexCross (polygon.edgeVector i)
              (polygon.edgeVector (i + 1)) < 0 ∧
        kwComplexCross (polygon.edgeVector (i + 2))
              (polygon.edgeVector (i + 3)) < 0)) :
    (polygon.rotate i).VertexOneCrossEar := by
  have hsum : polygon.edgeVector (i + 3) + polygon.edgeVector i +
      polygon.edgeVector (i + 1) + polygon.edgeVector (i + 2) = 0 := by
    have h := polygon.quadrilateral_edge_sum i
    linear_combination h
  have hbqRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear (i + 1)
  have hi : i + 1 + 1 = i + 2 := by
    rw [add_assoc]
    have h : (1 : Fin 4) + 1 = 2 := by decide
    rw [h]
  have hbq : kwComplexCross (polygon.edgeVector (i + 1))
      (polygon.edgeVector (i + 2)) ≠ 0 := by
    simpa only [hi] using hbqRaw
  have hcert := kw_fourVector_crossEar
    (polygon.edgeVector (i + 3)) (polygon.edgeVector i)
    (polygon.edgeVector (i + 1)) (polygon.edgeVector (i + 2))
    (polygon.edgeVector_ne_zero (i + 1))
    (polygon.edgeVector_ne_zero (i + 2)) hsum hbq hsign
  have hprev : (-1 : Fin 4) + i = i + 3 := by
    have hm : (-1 : Fin 4) = 3 := by decide
    rw [hm, add_comm]
  have h0 : (0 : Fin 4) + i = i := by simp
  have h1 : (1 : Fin 4) + i = i + 1 := by abel
  have h2 : (2 : Fin 4) + i = i + 2 := by abel
  simpa only [KWFiniteSimplePolygon.VertexOneCrossEar,
    KWFiniteSimplePolygon.rotate_edgeVector, hprev, h0, h1, h2] using hcert




theorem KWFiniteSimplePolygon.exists_rotated_vertexOneCrossEar_four
    (polygon : KWFiniteSimplePolygon 4)
    (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    ∃ r : Fin 4, (polygon.rotate r).VertexOneCrossEar := by
  let s0 := kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1)
  let s1 := kwComplexCross (polygon.edgeVector 1) (polygon.edgeVector 2)
  let s2 := kwComplexCross (polygon.edgeVector 2) (polygon.edgeVector 3)
  let s3 := kwComplexCross (polygon.edgeVector 3) (polygon.edgeVector 0)
  have h0 : s0 ≠ 0 :=
    polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear 0
  have h1 : s1 ≠ 0 :=
    polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear 1
  have h2 : s2 ≠ 0 :=
    polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear 2
  have h3 : s3 ≠ 0 :=
    polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear 3
  have hNo02 : ¬(s0 * s3 < 0 ∧ s1 * s2 < 0) :=
    polygon.quadrilateral_not_cross_pattern_zero_two
  have hNo13 : ¬(s1 * s0 < 0 ∧ s2 * s3 < 0) :=
    polygon.quadrilateral_not_cross_pattern_one_three
  rcases kw_four_signs_have_ear h0 h1 h2 h3 hNo02 hNo13 with
      h | h | h | h
  · refine ⟨0, polygon.rotated_vertexOneCrossEar_of_sign
      hnoncollinear 0 ?_⟩
    simpa [s0, s2, s3, Fin.add_def] using h
  · refine ⟨1, polygon.rotated_vertexOneCrossEar_of_sign
      hnoncollinear 1 ?_⟩
    simpa [s0, s1, s3, Fin.add_def] using h
  · refine ⟨2, polygon.rotated_vertexOneCrossEar_of_sign
      hnoncollinear 2 ?_⟩
    simpa [s0, s1, s2, Fin.add_def] using h
  · refine ⟨3, polygon.rotated_vertexOneCrossEar_of_sign
      hnoncollinear 3 ?_⟩
    simpa [s1, s2, s3, Fin.add_def] using h




theorem KWFiniteSimplePolygon.vertexOneDiagonalIsClean_four_of_crossEar
    (polygon : KWFiniteSimplePolygon 4)
    (hear : polygon.VertexOneCrossEar) :
    polygon.VertexOneDiagonalIsClean := by
  have he0 : polygon.edgeVector 0 =
      polygon.vertex 1 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he1 : polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 1 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he2 : polygon.edgeVector 2 =
      polygon.vertex 3 - polygon.vertex 2 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he3 : polygon.edgeVector 3 =
      polygon.vertex 0 - polygon.vertex 3 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have hdiag : polygon.edgeVector 0 + polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 0 := by
    rw [he0, he1]
    ring
  have hminus : (-1 : Fin 4) = 3 := by decide
  have hleft : kwComplexCross (polygon.edgeVector 3)
      (polygon.edgeVector 0 + polygon.edgeVector 1) ≠ 0 := by
    rw [← hminus]
    rcases hear.2.2.1 with h | h <;> nlinarith [h.2]
  have hright : kwComplexCross
      (polygon.edgeVector 0 + polygon.edgeVector 1)
      (polygon.edgeVector 2) ≠ 0 := by
    rcases hear.2.2.2 with h | h <;> nlinarith [h.2]
  have hv30 : polygon.vertex 3 - polygon.vertex 0 =
      -polygon.edgeVector 3 := by
    rw [he3]
    ring
  have hvertex3 : kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
      (polygon.vertex 3 - polygon.vertex 0) ≠ 0 := by
    rw [← hdiag, hv30, kwComplexCross_neg_right,
      kwComplexCross_swap]
    simpa using hleft
  constructor
  · intro k hk0 hk1 hk2
    fin_cases k
    · exact (hk0 rfl).elim
    · exact (hk1 rfl).elim
    · exact (hk2 rfl).elim
    · intro hbetween
      exact hvertex3 (kwComplexCross_eq_zero_of_sbtw hbetween)
  · intro k hk0 hk1
    fin_cases k
    · exact (hk0 rfl).elim
    · exact (hk1 rfl).elim
    · have hcross : kwComplexCross
          (polygon.vertex 0 - polygon.vertex 2)
          (polygon.vertex 3 - polygon.vertex 2) ≠ 0 := by
        intro hz
        apply hright
        have hv02 : polygon.vertex 0 - polygon.vertex 2 =
            -(polygon.vertex 2 - polygon.vertex 0) := by ring
        rw [hv02, ← hdiag, ← he2] at hz
        unfold kwComplexCross at hz ⊢
        simp only [Complex.neg_re, Complex.neg_im] at hz
        linear_combination -hz
      have hcommon :=
        kw_openSegments_disjoint_of_common_left_cross_ne hcross
      rw [Set.disjoint_left]
      intro z hzdiag hzedge
      exact Set.disjoint_left.mp hcommon
        ((sbtw_comm).mpr hzdiag) hzedge
    · have hcommon :=
        kw_openSegments_disjoint_of_common_left_cross_ne hvertex3
      rw [Set.disjoint_left]
      intro z hzdiag hzedge
      exact Set.disjoint_left.mp hcommon hzdiag
        ((sbtw_comm).mpr hzedge)



theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_crossEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneCrossEar) :
    polygon.VertexOnePhaseEar hm := by
  have hlocal := kwVectorTurnPhase_ear_splice
    (polygon.edgeVector (-1)) (polygon.edgeVector 0)
    (polygon.edgeVector 1) (polygon.edgeVector 2)
    (polygon.edgeVector_ne_zero (-1))
    (polygon.edgeVector_ne_zero 0)
    (polygon.edgeVector_ne_zero 1)
    (polygon.edgeVector_ne_zero 2)
    hear.1 hear.2.1 hear.2.2.1 hear.2.2.2
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal




theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_alignedSideEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (hear : polygon.VertexOneAlignedSideEar) :
    polygon.VertexOnePhaseEar hm := by
  have hpreviousRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear (-1)
  have hpreviousIndex : (-1 : Fin (m + 3)) + 1 = 0 := by abel
  have hprevious : kwComplexCross (polygon.edgeVector (-1))
      (polygon.edgeVector 0) ≠ 0 := by
    simpa only [hpreviousIndex] using hpreviousRaw
  have hnextRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear 1
  have hnextIndex : (1 : Fin (m + 3)) + 1 = 2 := by abel
  have hnext : kwComplexCross (polygon.edgeVector 1)
      (polygon.edgeVector 2) ≠ 0 := by
    simpa only [hnextIndex] using hnextRaw
  have hlocal := kwAngleTurnPhase_ear_splice_of_interiorSides
    (polygon.edgeVector (-1)) (polygon.edgeVector 0)
    (polygon.edgeVector 1) (polygon.edgeVector 2)
    (polygon.edgeVector_ne_zero (-1))
    (polygon.edgeVector_ne_zero 0)
    (polygon.edgeVector_ne_zero 1)
    (polygon.edgeVector_ne_zero 2)
    hprevious hear.2.1 hnext hear.2.2.1 hear.2.2.2
  change kwVectorTurnPhase (polygon.edgeVector (-1))
        (polygon.edgeVector 0) *
      kwVectorTurnPhase (polygon.edgeVector 0)
        (polygon.edgeVector 1) *
      kwVectorTurnPhase (polygon.edgeVector 1)
        (polygon.edgeVector 2) =
    kwVectorTurnPhase (polygon.edgeVector (-1))
        (polygon.edgeVector 0 + polygon.edgeVector 1) *
      kwVectorTurnPhase
        (polygon.edgeVector 0 + polygon.edgeVector 1)
        (polygon.edgeVector 2) at hlocal
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal



theorem KWFiniteSimplePolygon.vertexOneGeometricEar_of_alignedSideEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (hear : polygon.VertexOneAlignedSideEar) :
    polygon.VertexOneGeometricEar hm := by
  exact ⟨hear.1,
    polygon.vertexOnePhaseEar_of_alignedSideEar hm hnoncollinear hear⟩



theorem kwVectorTurnPhase_ear_splice_of_doubleNoWrap
    (previous incoming outgoing next : ℂ)
    (hi : incoming ≠ 0) (ho : outgoing ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hleft : kwAngleTurnNoWrap
      (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg (incoming + outgoing) : Real.Angle))
    (hright : kwAngleTurnNoWrap
      (Complex.arg (incoming + outgoing) : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  have hleftPhase := kwAngleTurnPhase_mul_of_sign_or_outer
    (Complex.arg previous : Real.Angle)
    (Complex.arg incoming : Real.Angle)
    (Complex.arg (incoming + outgoing) : Real.Angle)
    hleft.1 hleft.2.1 hleft.2.2
  have hrightPhase := kwAngleTurnPhase_mul_of_sign_or_outer
    (Complex.arg (incoming + outgoing) : Real.Angle)
    (Complex.arg outgoing : Real.Angle)
    (Complex.arg next : Real.Angle)
    hright.1 hright.2.1 hright.2.2
  have hmiddlePhase := kwAngleTurnPhase_vector_sum hi ho hmiddle
  change kwVectorTurnPhase previous incoming *
      kwVectorTurnPhase incoming (incoming + outgoing) =
        kwVectorTurnPhase previous (incoming + outgoing) at hleftPhase
  change kwVectorTurnPhase (incoming + outgoing) outgoing *
      kwVectorTurnPhase outgoing next =
        kwVectorTurnPhase (incoming + outgoing) next at hrightPhase
  change kwVectorTurnPhase incoming (incoming + outgoing) *
      kwVectorTurnPhase (incoming + outgoing) outgoing =
        kwVectorTurnPhase incoming outgoing at hmiddlePhase
  rw [← hmiddlePhase]
  calc
    kwVectorTurnPhase previous incoming *
          (kwVectorTurnPhase incoming (incoming + outgoing) *
            kwVectorTurnPhase (incoming + outgoing) outgoing) *
          kwVectorTurnPhase outgoing next =
        (kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming (incoming + outgoing)) *
          (kwVectorTurnPhase (incoming + outgoing) outgoing *
            kwVectorTurnPhase outgoing next) := by ring
    _ = kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next := by
      rw [hleftPhase, hrightPhase]



theorem kwVectorTurnPhase_ear_splice_of_doubleWrap
    (previous incoming outgoing next : ℂ)
    (hi : incoming ≠ 0) (ho : outgoing ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hleft : kwAngleTurnWrap
      (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg (incoming + outgoing) : Real.Angle))
    (hright : kwAngleTurnWrap
      (Complex.arg (incoming + outgoing) : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  have hleftPhase := kwAngleTurnPhase_mul_eq_neg_of_wrap
    (Complex.arg previous : Real.Angle)
    (Complex.arg incoming : Real.Angle)
    (Complex.arg (incoming + outgoing) : Real.Angle)
    hleft.1 hleft.2.1 hleft.2.2.1 hleft.2.2.2.1 hleft.2.2.2.2
  have hrightPhase := kwAngleTurnPhase_mul_eq_neg_of_wrap
    (Complex.arg (incoming + outgoing) : Real.Angle)
    (Complex.arg outgoing : Real.Angle)
    (Complex.arg next : Real.Angle)
    hright.1 hright.2.1 hright.2.2.1 hright.2.2.2.1 hright.2.2.2.2
  have hmiddlePhase := kwAngleTurnPhase_vector_sum hi ho hmiddle
  change kwVectorTurnPhase previous incoming *
      kwVectorTurnPhase incoming (incoming + outgoing) =
        -kwVectorTurnPhase previous (incoming + outgoing) at hleftPhase
  change kwVectorTurnPhase (incoming + outgoing) outgoing *
      kwVectorTurnPhase outgoing next =
        -kwVectorTurnPhase (incoming + outgoing) next at hrightPhase
  change kwVectorTurnPhase incoming (incoming + outgoing) *
      kwVectorTurnPhase (incoming + outgoing) outgoing =
        kwVectorTurnPhase incoming outgoing at hmiddlePhase
  rw [← hmiddlePhase]
  calc
    kwVectorTurnPhase previous incoming *
          (kwVectorTurnPhase incoming (incoming + outgoing) *
            kwVectorTurnPhase (incoming + outgoing) outgoing) *
          kwVectorTurnPhase outgoing next =
        (kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming (incoming + outgoing)) *
          (kwVectorTurnPhase (incoming + outgoing) outgoing *
            kwVectorTurnPhase outgoing next) := by ring
    _ = (-kwVectorTurnPhase previous (incoming + outgoing)) *
          (-kwVectorTurnPhase (incoming + outgoing) next) := by
      rw [hleftPhase, hrightPhase]
    _ = kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next := by ring



theorem kwVectorTurnPhase_ear_splice_of_mixedParity
    (previous incoming outgoing next : ℂ)
    (hi : incoming ≠ 0) (ho : outgoing ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hparity :
      (kwAngleTurnNoWrap (Complex.arg previous : Real.Angle)
            (Complex.arg incoming : Real.Angle)
            (Complex.arg (incoming + outgoing) : Real.Angle) ∧
          kwAngleTurnWrap
            (Complex.arg (incoming + outgoing) : Real.Angle)
            (Complex.arg outgoing : Real.Angle)
            (Complex.arg next : Real.Angle)) ∨
        (kwAngleTurnWrap (Complex.arg previous : Real.Angle)
            (Complex.arg incoming : Real.Angle)
            (Complex.arg (incoming + outgoing) : Real.Angle) ∧
          kwAngleTurnNoWrap
            (Complex.arg (incoming + outgoing) : Real.Angle)
            (Complex.arg outgoing : Real.Angle)
            (Complex.arg next : Real.Angle))) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      -(kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next) := by
  have hmiddlePhase := kwAngleTurnPhase_vector_sum hi ho hmiddle
  change kwVectorTurnPhase incoming (incoming + outgoing) *
      kwVectorTurnPhase (incoming + outgoing) outgoing =
        kwVectorTurnPhase incoming outgoing at hmiddlePhase
  rw [← hmiddlePhase]
  rcases hparity with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hleftPhase := kwAngleTurnPhase_mul_of_sign_or_outer
      (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg (incoming + outgoing) : Real.Angle)
      hleft.1 hleft.2.1 hleft.2.2
    have hrightPhase := kwAngleTurnPhase_mul_eq_neg_of_wrap
      (Complex.arg (incoming + outgoing) : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)
      hright.1 hright.2.1 hright.2.2.1
      hright.2.2.2.1 hright.2.2.2.2
    change kwVectorTurnPhase previous incoming *
        kwVectorTurnPhase incoming (incoming + outgoing) =
          kwVectorTurnPhase previous (incoming + outgoing) at hleftPhase
    change kwVectorTurnPhase (incoming + outgoing) outgoing *
        kwVectorTurnPhase outgoing next =
          -kwVectorTurnPhase (incoming + outgoing) next at hrightPhase
    calc
      kwVectorTurnPhase previous incoming *
            (kwVectorTurnPhase incoming (incoming + outgoing) *
              kwVectorTurnPhase (incoming + outgoing) outgoing) *
            kwVectorTurnPhase outgoing next =
          (kwVectorTurnPhase previous incoming *
              kwVectorTurnPhase incoming (incoming + outgoing)) *
            (kwVectorTurnPhase (incoming + outgoing) outgoing *
              kwVectorTurnPhase outgoing next) := by ring
      _ = _ := by rw [hleftPhase, hrightPhase]; ring
  · have hleftPhase := kwAngleTurnPhase_mul_eq_neg_of_wrap
      (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg (incoming + outgoing) : Real.Angle)
      hleft.1 hleft.2.1 hleft.2.2.1 hleft.2.2.2.1 hleft.2.2.2.2
    have hrightPhase := kwAngleTurnPhase_mul_of_sign_or_outer
      (Complex.arg (incoming + outgoing) : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)
      hright.1 hright.2.1 hright.2.2
    change kwVectorTurnPhase previous incoming *
        kwVectorTurnPhase incoming (incoming + outgoing) =
          -kwVectorTurnPhase previous (incoming + outgoing) at hleftPhase
    change kwVectorTurnPhase (incoming + outgoing) outgoing *
        kwVectorTurnPhase outgoing next =
          kwVectorTurnPhase (incoming + outgoing) next at hrightPhase
    calc
      kwVectorTurnPhase previous incoming *
            (kwVectorTurnPhase incoming (incoming + outgoing) *
              kwVectorTurnPhase (incoming + outgoing) outgoing) *
            kwVectorTurnPhase outgoing next =
          (kwVectorTurnPhase previous incoming *
              kwVectorTurnPhase incoming (incoming + outgoing)) *
            (kwVectorTurnPhase (incoming + outgoing) outgoing *
              kwVectorTurnPhase outgoing next) := by ring
      _ = _ := by rw [hleftPhase, hrightPhase]; ring


theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_doubleWrapEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneDoubleWrapEar) :
    polygon.VertexOnePhaseEar hm := by
  dsimp only [KWFiniteSimplePolygon.VertexOneDoubleWrapEar] at hear
  have hlocal := kwVectorTurnPhase_ear_splice_of_doubleWrap
    (polygon.edgeVector (-1)) (polygon.edgeVector 0)
    (polygon.edgeVector 1) (polygon.edgeVector 2)
    (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
    hear.2.1 hear.2.2.1 hear.2.2.2
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal



theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_strictParityEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneStrictParityEar) :
    polygon.VertexOnePhaseEar hm := by
  dsimp only [KWFiniteSimplePolygon.VertexOneStrictParityEar] at hear
  have hlocal :
      kwVectorTurnPhase (polygon.edgeVector (-1))
            (polygon.edgeVector 0) *
          kwVectorTurnPhase (polygon.edgeVector 0)
            (polygon.edgeVector 1) *
          kwVectorTurnPhase (polygon.edgeVector 1)
            (polygon.edgeVector 2) =
        kwVectorTurnPhase (polygon.edgeVector (-1))
            (polygon.edgeVector 0 + polygon.edgeVector 1) *
          kwVectorTurnPhase
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 2) := by
    rcases hear.2.2 with hnowrap | hwrap
    · exact kwVectorTurnPhase_ear_splice_of_doubleNoWrap
        (polygon.edgeVector (-1)) (polygon.edgeVector 0)
        (polygon.edgeVector 1) (polygon.edgeVector 2)
        (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
        hear.2.1 hnowrap.1 hnowrap.2
    · exact kwVectorTurnPhase_ear_splice_of_doubleWrap
        (polygon.edgeVector (-1)) (polygon.edgeVector 0)
        (polygon.edgeVector 1) (polygon.edgeVector 2)
        (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
        hear.2.1 hwrap.1 hwrap.2
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal


theorem KWFiniteSimplePolygon.vertexOneGeometricEar_of_strictParityEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneStrictParityEar) :
    polygon.VertexOneGeometricEar hm := by
  exact ⟨hear.1, polygon.vertexOnePhaseEar_of_strictParityEar hm hear⟩




theorem KWFiniteSimplePolygon.vertexOneStrictParityEar_of_geometricEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (hear : polygon.VertexOneGeometricEar hm) :
    polygon.VertexOneStrictParityEar := by
  have hmiddle := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear 0
  have h01 : (0 : Fin (m + 3)) + 1 = 1 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
  rw [h01] at hmiddle
  have hpreviousRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear (-1)
  have hpreviousIndex : (-1 : Fin (m + 3)) + 1 = 0 := by abel
  have hprevious : kwComplexCross (polygon.edgeVector (-1))
      (polygon.edgeVector 0) ≠ 0 := by
    simpa only [hpreviousIndex] using hpreviousRaw
  have hnextRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear 1
  have hnextIndex : (1 : Fin (m + 3)) + 1 = 2 := by abel
  have hnext : kwComplexCross (polygon.edgeVector 1)
      (polygon.edgeVector 2) ≠ 0 := by
    simpa only [hnextIndex] using hnextRaw
  have hdiagonal : polygon.edgeVector 0 + polygon.edgeVector 1 ≠ 0 := by
    intro hzero
    have : polygon.edgeVector 1 = -polygon.edgeVector 0 := by
      linear_combination hzero
    apply hmiddle
    rw [this]
    simp [kwComplexCross]
    ring
  have hincomingDiagonal : kwComplexCross (polygon.edgeVector 0)
      (polygon.edgeVector 0 + polygon.edgeVector 1) =
        kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) := by
    rw [kwComplexCross_add_right, kwComplexCross_self, zero_add]
  have hdiagonalOutgoing :
      kwComplexCross (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 1) =
        kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) := by
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have houter := polygon.outerTurns_ne_pi_of_diagonalIsClean hm hear.1
  let previous := (Complex.arg (polygon.edgeVector (-1)) : Real.Angle)
  let incoming := (Complex.arg (polygon.edgeVector 0) : Real.Angle)
  let diagonal :=
    (Complex.arg (polygon.edgeVector 0 + polygon.edgeVector 1) : Real.Angle)
  let outgoing := (Complex.arg (polygon.edgeVector 1) : Real.Angle)
  let next := (Complex.arg (polygon.edgeVector 2) : Real.Angle)
  have hleftCases : kwAngleTurnNoWrap previous incoming diagonal ∨
      kwAngleTurnWrap previous incoming diagonal := by
    apply kwAngleTurnNoWrap_or_wrap
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero
        (polygon.edgeVector_ne_zero (-1)) (polygon.edgeVector_ne_zero 0)
        hprevious
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero
        (polygon.edgeVector_ne_zero 0) hdiagonal
        (hincomingDiagonal.symm ▸ hmiddle)
    · exact houter.1
  have hrightCases : kwAngleTurnNoWrap diagonal outgoing next ∨
      kwAngleTurnWrap diagonal outgoing next := by
    apply kwAngleTurnNoWrap_or_wrap
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero hdiagonal
        (polygon.edgeVector_ne_zero 1)
        (hdiagonalOutgoing.symm ▸ hmiddle)
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero
        (polygon.edgeVector_ne_zero 1) (polygon.edgeVector_ne_zero 2) hnext
    · exact houter.2
  let phasePrevious : Fin (m + 3) := ⟨m + 1 + 1, by omega⟩
  have hphasePrevious : phasePrevious = (-1 : Fin (m + 3)) := by
    apply Fin.ext
    simp [phasePrevious, Fin.val_neg]
  dsimp only [KWFiniteSimplePolygon.VertexOneStrictParityEar]
  refine ⟨hear.1, hmiddle, ?_⟩
  rcases hleftCases with hleft | hleft <;>
      rcases hrightCases with hright | hright
  · exact Or.inl ⟨hleft, hright⟩
  · exfalso
    have hmixed := kwVectorTurnPhase_ear_splice_of_mixedParity
      (polygon.edgeVector (-1)) (polygon.edgeVector 0)
      (polygon.edgeVector 1) (polygon.edgeVector 2)
      (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
      hmiddle (Or.inl ⟨hleft, hright⟩)
    have hlocal : kwVectorTurnPhase (polygon.edgeVector phasePrevious)
          (polygon.edgeVector 0) *
        kwVectorTurnPhase (polygon.edgeVector 0) (polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 1) (polygon.edgeVector 2) =
      kwVectorTurnPhase (polygon.edgeVector phasePrevious)
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2) := by
      simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
        List.getLast_ofFn, hm, phasePrevious] using hear.2
    rw [hphasePrevious] at hlocal
    have hneg := hlocal.symm.trans hmixed
    have hzero : kwVectorTurnPhase (polygon.edgeVector (-1))
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2) = 0 := by
      linear_combination (1 / 2 : ℂ) * hneg
    exact (mul_ne_zero (kwVectorTurnPhase_ne_zero _ _)
      (kwVectorTurnPhase_ne_zero _ _)) hzero
  · exfalso
    have hmixed := kwVectorTurnPhase_ear_splice_of_mixedParity
      (polygon.edgeVector (-1)) (polygon.edgeVector 0)
      (polygon.edgeVector 1) (polygon.edgeVector 2)
      (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
      hmiddle (Or.inr ⟨hleft, hright⟩)
    have hlocal : kwVectorTurnPhase (polygon.edgeVector phasePrevious)
          (polygon.edgeVector 0) *
        kwVectorTurnPhase (polygon.edgeVector 0) (polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 1) (polygon.edgeVector 2) =
      kwVectorTurnPhase (polygon.edgeVector phasePrevious)
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2) := by
      simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
        List.getLast_ofFn, hm, phasePrevious] using hear.2
    rw [hphasePrevious] at hlocal
    have hneg := hlocal.symm.trans hmixed
    have hzero : kwVectorTurnPhase (polygon.edgeVector (-1))
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2) = 0 := by
      linear_combination (1 / 2 : ℂ) * hneg
    exact (mul_ne_zero (kwVectorTurnPhase_ne_zero _ _)
      (kwVectorTurnPhase_ne_zero _ _)) hzero
  · exact Or.inr ⟨hleft, hright⟩

theorem KWFiniteSimplePolygon.vertexOneStrictParityEar_iff_geometricEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    polygon.VertexOneStrictParityEar ↔
      polygon.VertexOneGeometricEar hm := by
  constructor
  · exact polygon.vertexOneGeometricEar_of_strictParityEar hm
  · exact polygon.vertexOneStrictParityEar_of_geometricEar
      hm hnoncollinear



theorem KWFiniteSimplePolygon.exists_rotated_vertexOneGeometricEar_four
    (polygon : KWFiniteSimplePolygon 4)
    (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    ∃ r : Fin 4,
      (polygon.rotate r).VertexOneGeometricEar (by omega) := by
  obtain ⟨r, hear⟩ :=
    polygon.exists_rotated_vertexOneCrossEar_four hnoncollinear
  exact ⟨r,
    (polygon.rotate r).vertexOneDiagonalIsClean_four_of_crossEar hear,
    (polygon.rotate r).vertexOnePhaseEar_of_crossEar (by omega) hear⟩



theorem KWFiniteSimplePolygon.removable_of_geometricEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneGeometricEar hm) :
    polygon.VertexOneRemovalIsSimple ∧ polygon.VertexOnePhaseEar hm := by
  exact ⟨polygon.vertexOneRemovalIsSimple_of_diagonalIsClean hear.1,
    hear.2⟩



theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_collinear
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hcol : Collinear ℝ
      ({polygon.vertex 0, polygon.vertex 1,
        polygon.vertex 2} : Set ℂ)) :
    polygon.VertexOnePhaseEar hm := by
  have hlocal := polygon.collinear_local_phase 0 hcol
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  simp only [zero_sub, zero_add] at hlocal
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal



theorem KWFiniteSimplePolygon.exists_removable_of_exists_collinear
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hcol : ∃ i : Fin (m + 3), Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    ∃ r : Fin (m + 3),
      (polygon.rotate r).VertexOneRemovalIsSimple ∧
        (polygon.rotate r).VertexOnePhaseEar hm := by
  obtain ⟨i, hi⟩ := hcol
  refine ⟨i, ?_⟩
  have hrot : Collinear ℝ
      ({(polygon.rotate i).vertex 0, (polygon.rotate i).vertex 1,
        (polygon.rotate i).vertex 2} : Set ℂ) := by
    simpa [KWFiniteSimplePolygon.rotate, add_comm] using hi
  have hbetween :=
    (polygon.rotate i).consecutive_wbtw_of_collinear 0 hrot
  constructor
  · exact (polygon.rotate i).vertexOneRemovalIsSimple_of_between hbetween
  · exact (polygon.rotate i).vertexOnePhaseEar_of_collinear hm hrot



theorem KWFiniteSimplePolygon.exists_removable_of_noncollinear_case
    (hgeneric : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  intro m hm polygon
  by_cases hcol : ∃ i : Fin (m + 3), Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)
  · exact polygon.exists_removable_of_exists_collinear hm hcol
  · apply hgeneric m hm polygon
    simpa only [not_exists] using hcol




theorem KWFiniteSimplePolygon.exists_removable_of_geometricEar_case
    (hgeneric : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar hm) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  apply KWFiniteSimplePolygon.exists_removable_of_noncollinear_case
  intro m hm polygon hnoncollinear
  obtain ⟨r, hear⟩ := hgeneric m hm polygon hnoncollinear
  exact ⟨r, (polygon.rotate r).removable_of_geometricEar hm hear⟩



theorem KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
    (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar (by omega)) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  apply KWFiniteSimplePolygon.exists_removable_of_geometricEar_case
  intro m hm polygon hnoncollinear
  rcases eq_or_lt_of_le hm with rfl | hmTwo
  · simpa using polygon.exists_rotated_vertexOneGeometricEar_four
      hnoncollinear
  · exact hgeneric m hmTwo polygon hnoncollinear




theorem KWFiniteSimplePolygon.exists_removable_of_alignedSideEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneAlignedSideEar) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  apply KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
  intro m hm polygon hnoncollinear
  obtain ⟨r, hear⟩ := hgeneric m hm polygon hnoncollinear
  refine ⟨r, (polygon.rotate r).vertexOneGeometricEar_of_alignedSideEar
    (by omega) ?_ hear⟩
  exact polygon.rotate_not_collinear hnoncollinear r



theorem KWFiniteSimplePolygon.exists_removable_of_strictParityEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneStrictParityEar) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  apply KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
  intro m hm polygon hnoncollinear
  obtain ⟨r, hear⟩ := hgeneric m hm polygon hnoncollinear
  exact ⟨r, (polygon.rotate r).vertexOneGeometricEar_of_strictParityEar
    (by omega) hear⟩



theorem kwVectorPhasePath_contract_ear
    (previous incoming outgoing next : ℂ) (tail : List ℂ)
    (hp : previous ≠ 0) (hi : incoming ≠ 0)
    (ho : outgoing ≠ 0) (hn : next ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hrightTurn :
      (Complex.arg next : Real.Angle) -
        (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
    (hleft :
      (0 < kwComplexCross previous incoming ∧
          0 < kwComplexCross previous (incoming + outgoing)) ∨
        (kwComplexCross previous incoming < 0 ∧
          kwComplexCross previous (incoming + outgoing) < 0))
    (hright :
      (0 < kwComplexCross (incoming + outgoing) outgoing ∧
          0 < kwComplexCross (incoming + outgoing) next) ∨
        (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
          kwComplexCross (incoming + outgoing) next < 0)) :
    kwVectorPhasePath (previous :: incoming :: outgoing :: next :: tail) =
      kwVectorPhasePath
        (previous :: (incoming + outgoing) :: next :: tail) := by
  simp only [kwVectorPhasePath_cons_cons]
  have hlocal := kwVectorTurnPhase_ear_splice
    previous incoming outgoing next hp hi ho hn hmiddle hrightTurn hleft hright
  calc
    kwVectorTurnPhase previous incoming *
          (kwVectorTurnPhase incoming outgoing *
            (kwVectorTurnPhase outgoing next *
              kwVectorPhasePath (next :: tail))) =
        (kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next) *
          kwVectorPhasePath (next :: tail) := by ring
    _ = (kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next) *
        kwVectorPhasePath (next :: tail) := by rw [hlocal]
    _ = kwVectorTurnPhase previous (incoming + outgoing) *
        (kwVectorTurnPhase (incoming + outgoing) next *
          kwVectorPhasePath (next :: tail)) := by ring



theorem kwVectorPhasePath_contract_of_local
    (previous incoming outgoing next : ℂ) (tail : List ℂ)
    (hlocal :
      kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next =
        kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next) :
    kwVectorPhasePath (previous :: incoming :: outgoing :: next :: tail) =
      kwVectorPhasePath
        (previous :: (incoming + outgoing) :: next :: tail) := by
  simp only [kwVectorPhasePath_cons_cons]
  calc
    kwVectorTurnPhase previous incoming *
          (kwVectorTurnPhase incoming outgoing *
            (kwVectorTurnPhase outgoing next *
              kwVectorPhasePath (next :: tail))) =
        (kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next) *
          kwVectorPhasePath (next :: tail) := by ring
    _ = (kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next) *
        kwVectorPhasePath (next :: tail) := by rw [hlocal]
    _ = kwVectorTurnPhase previous (incoming + outgoing) *
        (kwVectorTurnPhase (incoming + outgoing) next *
          kwVectorPhasePath (next :: tail)) := by ring




theorem kwVectorPhaseCycle_contract_ear
    (previous incoming outgoing next : ℂ) (tail : List ℂ)
    (hp : previous ≠ 0) (hi : incoming ≠ 0)
    (ho : outgoing ≠ 0) (hn : next ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hrightTurn :
      (Complex.arg next : Real.Angle) -
        (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
    (hleft :
      (0 < kwComplexCross previous incoming ∧
          0 < kwComplexCross previous (incoming + outgoing)) ∨
        (kwComplexCross previous incoming < 0 ∧
          kwComplexCross previous (incoming + outgoing) < 0))
    (hright :
      (0 < kwComplexCross (incoming + outgoing) outgoing ∧
          0 < kwComplexCross (incoming + outgoing) next) ∨
        (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
          kwComplexCross (incoming + outgoing) next < 0)) :
    kwVectorPhaseCycle (previous :: incoming :: outgoing :: next :: tail) =
      kwVectorPhaseCycle
        (previous :: (incoming + outgoing) :: next :: tail) := by
  simp only [kwVectorPhaseCycle_cons]
  rw [kwVectorPhasePath_contract_ear previous incoming outgoing next tail
    hp hi ho hn hmiddle hrightTurn hleft hright]
  simp


theorem kwVectorPhaseCycle_contract_of_local
    (previous incoming outgoing next : ℂ) (tail : List ℂ)
    (hlocal :
      kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next =
        kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next) :
    kwVectorPhaseCycle (previous :: incoming :: outgoing :: next :: tail) =
      kwVectorPhaseCycle
        (previous :: (incoming + outgoing) :: next :: tail) := by
  simp only [kwVectorPhaseCycle_cons]
  rw [kwVectorPhasePath_contract_of_local
    previous incoming outgoing next tail hlocal]
  simp




inductive KWVectorEarDecomposition : List ℂ → Prop
  | triangle (x y z : ℂ)
      (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
      (hsum : x + y + z = 0)
      (hcross : kwComplexCross x y ≠ 0) :
      KWVectorEarDecomposition [x, y, z]
  | contract (previous incoming outgoing next : ℂ) (tail : List ℂ)
      (hp : previous ≠ 0) (hi : incoming ≠ 0)
      (ho : outgoing ≠ 0) (hn : next ≠ 0)
      (hmiddle : kwComplexCross incoming outgoing ≠ 0)
      (hrightTurn :
        (Complex.arg next : Real.Angle) -
          (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
      (hleft :
        (0 < kwComplexCross previous incoming ∧
            0 < kwComplexCross previous (incoming + outgoing)) ∨
          (kwComplexCross previous incoming < 0 ∧
            kwComplexCross previous (incoming + outgoing) < 0))
      (hright :
        (0 < kwComplexCross (incoming + outgoing) outgoing ∧
            0 < kwComplexCross (incoming + outgoing) next) ∨
          (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
            kwComplexCross (incoming + outgoing) next < 0))
      (reduced : KWVectorEarDecomposition
        (previous :: (incoming + outgoing) :: next :: tail)) :
      KWVectorEarDecomposition
        (previous :: incoming :: outgoing :: next :: tail)
  | contractPhase (previous incoming outgoing next : ℂ) (tail : List ℂ)
      (hlocal :
        kwVectorTurnPhase previous incoming *
              kwVectorTurnPhase incoming outgoing *
              kwVectorTurnPhase outgoing next =
          kwVectorTurnPhase previous (incoming + outgoing) *
            kwVectorTurnPhase (incoming + outgoing) next)
      (reduced : KWVectorEarDecomposition
        (previous :: (incoming + outgoing) :: next :: tail)) :
      KWVectorEarDecomposition
        (previous :: incoming :: outgoing :: next :: tail)
  | rotate (edges : List ℂ) (r : ℕ)
      (decomposition : KWVectorEarDecomposition edges) :
      KWVectorEarDecomposition (edges.rotate r)




theorem KWVectorEarDecomposition.expand_front
    (incoming outgoing next : ℂ) (tail : List ℂ) (previous : ℂ)
    (hlocal :
      kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next =
        kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next)
    (hreduced : KWVectorEarDecomposition
      ((incoming + outgoing) :: next :: tail ++ [previous])) :
    KWVectorEarDecomposition
      (incoming :: outgoing :: next :: tail ++ [previous]) := by
  have hrotateReduced : KWVectorEarDecomposition
      (previous :: (incoming + outgoing) :: next :: tail) := by
    have h := KWVectorEarDecomposition.rotate
      (((incoming + outgoing) :: next :: tail) ++ [previous])
      ((incoming + outgoing) :: next :: tail).length hreduced
    rw [List.rotate_append_length_eq] at h
    simpa using h
  have hcontracted : KWVectorEarDecomposition
      (previous :: incoming :: outgoing :: next :: tail) :=
    .contractPhase previous incoming outgoing next tail hlocal hrotateReduced
  have h := KWVectorEarDecomposition.rotate
    ([previous] ++ incoming :: outgoing :: next :: tail) 1 hcontracted
  rw [show 1 = [previous].length by simp,
    List.rotate_append_length_eq] at h
  simpa using h


theorem KWVectorEarDecomposition.of_rotate
    (edges : List ℂ) (r : ℕ)
    (h : KWVectorEarDecomposition (edges.rotate r)) :
    KWVectorEarDecomposition edges := by
  have hrot : edges ~r edges.rotate r := ⟨r, rfl⟩
  obtain ⟨s, hs⟩ := hrot.symm
  have hback := KWVectorEarDecomposition.rotate (edges.rotate r) s h
  rw [hs] at hback
  exact hback



theorem KWVectorEarDecomposition.expand_front_remaining
    (incoming outgoing : ℂ) (remaining : List ℂ)
    (hne : remaining ≠ []) (htail : remaining.tail ≠ [])
    (hlocal :
      kwVectorTurnPhase (remaining.tail.getLast htail) incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing (remaining.head hne) =
        kwVectorTurnPhase (remaining.tail.getLast htail)
            (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) (remaining.head hne))
    (hreduced : KWVectorEarDecomposition
      ((incoming + outgoing) :: remaining)) :
    KWVectorEarDecomposition (incoming :: outgoing :: remaining) := by
  obtain ⟨next, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hrest : rest ≠ [] := by simpa using htail
  rw [← rest.dropLast_append_getLast hrest] at hreduced ⊢
  apply KWVectorEarDecomposition.expand_front
  · simpa using hlocal
  · simpa using hreduced



theorem KWVectorEarDecomposition.of_removeVertexOne
    {m : ℕ} (hm : 1 ≤ m) (vertex : Fin (m + 3) → ℂ)
    (hlocal :
      let remaining := List.ofFn (fun i : Fin (m + 1) ↦
        kwCyclicEdgeVector vertex i.succ.succ)
      kwVectorTurnPhase (remaining.tail.getLast (by
            simp [remaining]; omega)) (kwCyclicEdgeVector vertex 0) *
          kwVectorTurnPhase (kwCyclicEdgeVector vertex 0)
            (kwCyclicEdgeVector vertex 1) *
          kwVectorTurnPhase (kwCyclicEdgeVector vertex 1)
            (remaining.head (by simp [remaining])) =
        kwVectorTurnPhase (remaining.tail.getLast (by
            simp [remaining]; omega))
              (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1) *
          kwVectorTurnPhase
            (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1)
            (remaining.head (by simp [remaining])))
    (hreduced : KWVectorEarDecomposition
      (kwCyclicEdgeList (kwRemoveVertexOne vertex))) :
    KWVectorEarDecomposition (kwCyclicEdgeList vertex) := by
  let remaining := List.ofFn (fun i : Fin (m + 1) ↦
    kwCyclicEdgeVector vertex i.succ.succ)
  have hne : remaining ≠ [] := by simp [remaining]
  have htail : remaining.tail ≠ [] := by simp [remaining]; omega
  rw [kwCyclicEdgeList_removeVertexOne] at hreduced
  rw [kwCyclicEdgeList_eq_first_two]
  apply KWVectorEarDecomposition.expand_front_remaining
    (kwCyclicEdgeVector vertex 0) (kwCyclicEdgeVector vertex 1)
    remaining hne htail
  · simpa only [remaining] using hlocal
  · simpa only [remaining] using hreduced



theorem KWFiniteSimplePolygon.earDecomposition_of_removeVertexOne
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple)
    (hphase : polygon.VertexOnePhaseEar hm)
    (hreduced : KWVectorEarDecomposition
      (polygon.removeVertexOne hm hsimple).edgeList) :
    KWVectorEarDecomposition polygon.edgeList := by
  rw [KWFiniteSimplePolygon.edgeList_eq_cyclic] at hreduced ⊢
  change KWVectorEarDecomposition
    (kwCyclicEdgeList (kwRemoveVertexOne polygon.vertex)) at hreduced
  apply KWVectorEarDecomposition.of_removeVertexOne hm polygon.vertex
  · simpa only [KWFiniteSimplePolygon.VertexOnePhaseEar,
      KWFiniteSimplePolygon.edgeVector_eq_cyclic] using hphase
  · exact hreduced



theorem KWFiniteSimplePolygon.earDecomposition_three
    (polygon : KWFiniteSimplePolygon 3) :
    KWVectorEarDecomposition polygon.edgeList := by
  let x := polygon.edgeVector 0
  let y := polygon.edgeVector 1
  let z := polygon.edgeVector 2
  have hx : x ≠ 0 := polygon.edgeVector_ne_zero 0
  have hy : y ≠ 0 := polygon.edgeVector_ne_zero 1
  have hz : z ≠ 0 := polygon.edgeVector_ne_zero 2
  have hsum : x + y + z = 0 := by
    have h01 : (0 : Fin 3) + 1 = 1 := by decide
    have h12 : (1 : Fin 3) + 1 = 2 := by decide
    have h20 : (2 : Fin 3) + 1 = 0 := by decide
    simp only [x, y, z, KWFiniteSimplePolygon.edgeVector,
      h01, h12, h20]
    ring
  have hcross : kwComplexCross x y ≠ 0 := by
    intro hzero
    apply polygon.not_collinear_three
    apply kw_collinear_of_cross_sub_eq_zero
    have h01 : (0 : Fin 3) + 1 = 1 := by decide
    have h12 : (1 : Fin 3) + 1 = 2 := by decide
    simpa only [x, y, KWFiniteSimplePolygon.edgeVector,
      h01, h12] using hzero
  have htriangle : KWVectorEarDecomposition [x, y, z] :=
    .triangle x y z hx hy hz hsum hcross
  simpa only [KWFiniteSimplePolygon.edgeList, List.ofFn_succ,
    List.ofFn_zero, Fin.isValue, x, y, z] using htriangle




theorem KWFiniteSimplePolygon.earDecomposition_of_exists_removable
    (hexists : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm) :
    ∀ (k : ℕ) (polygon : KWFiniteSimplePolygon (k + 3)),
      KWVectorEarDecomposition polygon.edgeList := by
  intro k
  induction k with
  | zero =>
      intro polygon
      simpa using polygon.earDecomposition_three
  | succ k ih =>
      intro polygon
      have hm : 1 ≤ k + 1 := by omega
      obtain ⟨r, hsimple, hphase⟩ := hexists (k + 1) hm polygon
      let rotated := polygon.rotate r
      have hreduced : KWVectorEarDecomposition
          (rotated.removeVertexOne hm hsimple).edgeList := by
        simpa [rotated] using ih (rotated.removeVertexOne hm hsimple)
      have hrotated : KWVectorEarDecomposition rotated.edgeList :=
        rotated.earDecomposition_of_removeVertexOne hm hsimple hphase hreduced
      change KWVectorEarDecomposition (polygon.rotate r).edgeList at hrotated
      rw [polygon.rotate_edgeList] at hrotated
      exact KWVectorEarDecomposition.of_rotate polygon.edgeList r.val hrotated


theorem KWFiniteSimplePolygon.earDecomposition_of_exists_removable_all
    (hexists : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm)
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    KWVectorEarDecomposition polygon.edgeList := by
  have hthree := polygon.three_le
  obtain ⟨k, hk⟩ : ∃ k, n = k + 3 :=
    ⟨n - 3, by omega⟩
  subst n
  exact KWFiniteSimplePolygon.earDecomposition_of_exists_removable
    hexists k polygon



theorem KWFiniteSimplePolygon.earDecomposition_of_geometricEar_five_plus
    (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar (by omega))
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    KWVectorEarDecomposition polygon.edgeList :=
  polygon.earDecomposition_of_exists_removable_all
    (KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
      hgeneric)



theorem KWFiniteSimplePolygon.earDecomposition_of_alignedSideEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneAlignedSideEar)
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    KWVectorEarDecomposition polygon.edgeList :=
  polygon.earDecomposition_of_exists_removable_all
    (KWFiniteSimplePolygon.exists_removable_of_alignedSideEar_five_plus
      hgeneric)


theorem kwVectorPhaseCycle_triangle_eq_neg_one
    (x y z : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0)
    (hcross : kwComplexCross x y ≠ 0) :
    kwVectorPhaseCycle [x, y, z] = -1 := by
  have hsign := kw_triangle_edgeAngles_same_sign hx hy hz hsum hcross
  have hphase := kw_three_principal_halfAngle_product_eq_neg_one
    (Complex.arg x : Real.Angle) (Complex.arg y : Real.Angle)
    (Complex.arg z : Real.Angle) hsign
  simpa only [kwVectorPhaseCycle, kwVectorPhasePath,
    kwVectorTurnPhase, kwAngleTurnPhase, List.getLastD_cons,
    List.getLastD_nil, one_mul, mul_one, mul_assoc] using hphase



theorem KWVectorEarDecomposition.phaseCycle_eq_neg_one
    {edges : List ℂ} (h : KWVectorEarDecomposition edges) :
    kwVectorPhaseCycle edges = -1 := by
  induction h with
  | triangle x y z hx hy hz hsum hcross =>
      exact kwVectorPhaseCycle_triangle_eq_neg_one
        x y z hx hy hz hsum hcross
  | contract previous incoming outgoing next tail hp hi ho hn hmiddle
      hrightTurn hleft hright reduced ih =>
      rw [kwVectorPhaseCycle_contract_ear previous incoming outgoing next tail
        hp hi ho hn hmiddle hrightTurn hleft hright]
      exact ih
  | contractPhase previous incoming outgoing next tail hlocal reduced ih =>
      rw [kwVectorPhaseCycle_contract_of_local
        previous incoming outgoing next tail hlocal]
      exact ih
  | rotate edges r decomposition ih =>
      rw [kwVectorPhaseCycle_rotate]
      exact ih



def KWStraightLineCycleEarDecomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : Prop :=
  ∀ {root : V} (p : G.Walk root root) (_hp : p.IsCycle),
    KWVectorEarDecomposition (List.ofFn fun k : Fin p.darts.length ↦
      embedding.vertex (kwGraphCycleDartLoop p k).snd -
        embedding.vertex (kwGraphCycleDartLoop p k).fst)



theorem KWStraightLineCycleEarDecomposition.of_exists_removable
    (hexists : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm)
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleEarDecomposition G embedding := by
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [← embedding.cyclePolygon_edgeList p hp]
  exact KWFiniteSimplePolygon.earDecomposition_of_exists_removable_all
    hexists (embedding.cyclePolygon p hp)




theorem KWStraightLineCycleEarDecomposition.of_geometricEar_five_plus
    (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar (by omega))
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleEarDecomposition G embedding :=
  KWStraightLineCycleEarDecomposition.of_exists_removable
    (KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
      hgeneric) embedding



theorem KWStraightLineCycleEarDecomposition.of_alignedSideEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneAlignedSideEar)
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleEarDecomposition G embedding :=
  KWStraightLineCycleEarDecomposition.of_exists_removable
    (KWFiniteSimplePolygon.exists_removable_of_alignedSideEar_five_plus
      hgeneric) embedding



theorem KWStraightLineCycleEarDecomposition.phaseProduct_eq_neg_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (h : KWStraightLineCycleEarDecomposition G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [← embedding.vectorPhaseCycle_of_dartLoop (kwGraphCycleDartLoop p)]
  exact (h p hp).phaseCycle_eq_neg_one

end StatMech.FrontierA
