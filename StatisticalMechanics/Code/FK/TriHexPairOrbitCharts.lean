/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexPeriodicCrossingGeometry








open SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice


def siteLexNonnegative (d : Site 2) : Prop :=
  0 < d 0 ∨ d 0 = 0 ∧ 0 <= d 1

instance siteLexNonnegative_decidable (d : Site 2) :
    Decidable (siteLexNonnegative d) := by
  unfold siteLexNonnegative
  infer_instance

theorem siteLexNonnegative_zero :
    siteLexNonnegative (0 : Site 2) := by
  right
  simp

theorem siteLexNonnegative_neg_of_not
    {d : Site 2} (h : ¬ siteLexNonnegative d) :
    siteLexNonnegative (-d) := by
  unfold siteLexNonnegative at h ⊢
  simp only [Pi.neg_apply]
  by_cases h0 : d 0 = 0
  · right
    constructor
    · simp [h0]
    · have h1 : ¬ 0 <= d 1 := by tauto
      omega
  · left
    have hle : d 0 <= 0 := by omega
    omega

theorem not_siteLexNonnegative_neg_of_ne_zero
    {d : Site 2} (hd : d ≠ 0) (h : siteLexNonnegative d) :
    ¬ siteLexNonnegative (-d) := by
  unfold siteLexNonnegative at h ⊢
  simp only [Pi.neg_apply]
  intro hn
  by_cases h0 : d 0 = 0
  · have h1 : d 1 ≠ 0 := by
      intro h1
      apply hd
      funext k
      fin_cases k <;> simp [h0, h1]
    rcases h with hpos | ⟨_, hnonneg⟩
    · omega
    rcases hn with hneg | ⟨_, hnonpos⟩
    · omega
    · omega
  · rcases h with hpos | ⟨hz, _⟩
    · rcases hn with hneg | ⟨hz', _⟩ <;> omega
    · exact h0 hz


abbrev TriangularPairShape := {d : Site 2 // siteLexNonnegative d}

def triangularPairNormal (x y : Site 2) :
    Site 2 × TriangularPairShape :=
  if h : siteLexNonnegative (y - x) then (x, ⟨y - x, h⟩)
  else (y, ⟨x - y, by
    have := siteLexNonnegative_neg_of_not h
    simpa only [neg_sub] using this⟩)

theorem triangularPairNormal_symm (x y : Site 2) :
    triangularPairNormal x y = triangularPairNormal y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    by_cases h : siteLexNonnegative (y - x)
    · have hn := not_siteLexNonnegative_neg_of_ne_zero hd h
      have hn' : ¬ siteLexNonnegative (x - y) := by
        simpa only [neg_sub] using hn
      simp only [triangularPairNormal, h, hn', dite_true, dite_false]
    · have hr : siteLexNonnegative (x - y) := by
        have := siteLexNonnegative_neg_of_not h
        simpa only [neg_sub] using this
      simp only [triangularPairNormal, h, hr, dite_true, dite_false]


def triangularPairOrbitTo : Sym2 (Site 2) →
    Site 2 × TriangularPairShape :=
  Sym2.lift ⟨triangularPairNormal, triangularPairNormal_symm⟩

@[simp] theorem triangularPairOrbitTo_mk (x y : Site 2) :
    triangularPairOrbitTo s(x, y) = triangularPairNormal x y := by
  exact Sym2.lift_mk _ _ _


def triangularPairOrbitFrom
    (a : Site 2 × TriangularPairShape) : Sym2 (Site 2) :=
  s(a.1, a.1 + a.2.1)

theorem triangularPairOrbitFrom_to (e : Sym2 (Site 2)) :
    triangularPairOrbitFrom (triangularPairOrbitTo e) = e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [triangularPairOrbitTo_mk]
      unfold triangularPairNormal triangularPairOrbitFrom
      split_ifs
      · congr 1
        ext k
        simp
      · rw [show y + (x - y) = x by abel]
        exact Sym2.eq_swap

theorem triangularPairOrbitTo_from
    (a : Site 2 × TriangularPairShape) :
    triangularPairOrbitTo (triangularPairOrbitFrom a) = a := by
  rcases a with ⟨x, d, hd⟩
  rw [show triangularPairOrbitFrom (x, ⟨d, hd⟩) = s(x, x + d) by rfl]
  rw [triangularPairOrbitTo_mk]
  unfold triangularPairNormal
  simp only [add_sub_cancel_left, hd, dite_true]


def triangularPairOrbitEquiv :
    Sym2 (Site 2) ≃ Site 2 × TriangularPairShape where
  toFun := triangularPairOrbitTo
  invFun := triangularPairOrbitFrom
  left_inv := triangularPairOrbitFrom_to
  right_inv := triangularPairOrbitTo_from

theorem triangularPairNormal_add (z x y : Site 2) :
    triangularPairNormal (x + z) (y + z) =
      (triangularPairNormal x y).map (fun b => b + z) id := by
  unfold triangularPairNormal
  have hsub : y + z - (x + z) = y - x := by abel
  have hsub' : x + z - (y + z) = x - y := by abel
  simp only [hsub, hsub']
  split_ifs <;> rfl

theorem triangularPairOrbitEquiv_add (z : Site 2)
    (e : Sym2 (Site 2)) :
    triangularPairOrbitEquiv (Sym2.map (siteTranslate z) e) =
      (triangularPairOrbitEquiv e).map (fun b => b + z) id := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [triangularPairOrbitEquiv, Equiv.coe_fn_mk,
        Sym2.map_mk, siteTranslate_apply, triangularPairOrbitTo_mk]
      exact triangularPairNormal_add z x y




def siteLexPositive (d : Site 2) : Prop :=
  0 < d 0 ∨ d 0 = 0 ∧ 0 < d 1

instance siteLexPositive_decidable (d : Site 2) :
    Decidable (siteLexPositive d) := by
  unfold siteLexPositive
  infer_instance

theorem not_siteLexPositive_neg_of_pos {d : Site 2}
    (h : siteLexPositive d) : ¬ siteLexPositive (-d) := by
  unfold siteLexPositive at h ⊢
  simp only [Pi.neg_apply]
  omega

theorem site_eq_zero_of_not_lexPositive_or_neg {d : Site 2}
    (h : ¬ siteLexPositive d) (hn : ¬ siteLexPositive (-d)) :
    d = 0 := by
  unfold siteLexPositive at h hn
  simp only [Pi.neg_apply] at hn
  have h0 : d 0 = 0 := by omega
  have h1 : d 1 = 0 := by omega
  funext k
  fin_cases k <;> simp [h0, h1]


def boolOrdered (b c : Bool) : Prop := b = false ∨ c = true

instance boolOrdered_decidable (b c : Bool) : Decidable (boolOrdered b c) :=
  by
    unfold boolOrdered
    infer_instance



abbrev HexagonalPairShape :=
  ({d : Site 2 // siteLexPositive d} × Bool × Bool) ⊕
    {bc : Bool × Bool // boolOrdered bc.1 bc.2}

def hexagonalPairNormal (u v : HexVertex) :
    Site 2 × HexagonalPairShape :=
  if h : siteLexPositive (v.1 - u.1) then
    (u.1, Sum.inl (⟨v.1 - u.1, h⟩, u.2, v.2))
  else if hr : siteLexPositive (u.1 - v.1) then
    (v.1, Sum.inl (⟨u.1 - v.1, hr⟩, v.2, u.2))
  else if hb : boolOrdered u.2 v.2 then
    (u.1, Sum.inr ⟨(u.2, v.2), hb⟩)
  else
    (v.1, Sum.inr ⟨(v.2, u.2), by
      rcases u with ⟨x, b⟩
      rcases v with ⟨y, c⟩
      cases b <;> cases c <;> simp [boolOrdered] at hb ⊢⟩)

theorem hexagonalPairNormal_symm (u v : HexVertex) :
    hexagonalPairNormal u v = hexagonalPairNormal v u := by
  by_cases h : siteLexPositive (v.1 - u.1)
  · have hn : ¬ siteLexPositive (u.1 - v.1) := by
      have := not_siteLexPositive_neg_of_pos h
      simpa only [neg_sub] using this
    simp [hexagonalPairNormal, h, hn]
  · by_cases hr : siteLexPositive (u.1 - v.1)
    · simp [hexagonalPairNormal, h, hr]
    · have hz : v.1 - u.1 = 0 := by
        apply site_eq_zero_of_not_lexPositive_or_neg h
        simpa only [neg_sub] using hr
      have hvu : v.1 = u.1 := sub_eq_zero.mp hz
      have huv : u.1 = v.1 := hvu.symm
      rcases u with ⟨x, b⟩
      rcases v with ⟨y, c⟩
      simp only at huv
      subst y
      cases b <;> cases c <;>
        simp [hexagonalPairNormal, siteLexPositive, boolOrdered]


def hexagonalPairOrbitTo : Sym2 HexVertex →
    Site 2 × HexagonalPairShape :=
  Sym2.lift ⟨hexagonalPairNormal, hexagonalPairNormal_symm⟩

@[simp] theorem hexagonalPairOrbitTo_mk (u v : HexVertex) :
    hexagonalPairOrbitTo s(u, v) = hexagonalPairNormal u v := by
  exact Sym2.lift_mk _ _ _


def hexagonalPairOrbitFrom
    (a : Site 2 × HexagonalPairShape) : Sym2 HexVertex :=
  match a.2 with
  | Sum.inl s => s((a.1, s.2.1), (a.1 + s.1.1, s.2.2))
  | Sum.inr s => s((a.1, s.1.1), (a.1, s.1.2))

theorem hexagonalPairOrbitFrom_to (e : Sym2 HexVertex) :
    hexagonalPairOrbitFrom (hexagonalPairOrbitTo e) = e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [hexagonalPairOrbitTo_mk]
      unfold hexagonalPairNormal
      split_ifs with h hr hb
      · simp only [hexagonalPairOrbitFrom]
        congr 1
        apply Prod.ext
        · simp
        · rfl
      · simp only [hexagonalPairOrbitFrom]
        rw [show v.1 + (u.1 - v.1) = u.1 by abel]
        exact Sym2.eq_swap
      · have hz : v.1 - u.1 = 0 := by
          apply site_eq_zero_of_not_lexPositive_or_neg h
          simpa only [neg_sub] using hr
        have hvu : v.1 = u.1 := sub_eq_zero.mp hz
        rcases u with ⟨ux, ub⟩
        rcases v with ⟨vx, vb⟩
        simp only at hvu
        subst vx
        simp only [hexagonalPairOrbitFrom]
      · have hz : v.1 - u.1 = 0 := by
          apply site_eq_zero_of_not_lexPositive_or_neg h
          simpa only [neg_sub] using hr
        have hvu : v.1 = u.1 := sub_eq_zero.mp hz
        rcases u with ⟨ux, ub⟩
        rcases v with ⟨vx, vb⟩
        simp only at hvu
        subst vx
        simp only [hexagonalPairOrbitFrom]
        exact Sym2.eq_swap

theorem hexagonalPairOrbitTo_from
    (a : Site 2 × HexagonalPairShape) :
    hexagonalPairOrbitTo (hexagonalPairOrbitFrom a) = a := by
  rcases a with ⟨x, s⟩
  rcases s with s | s
  · rcases s with ⟨d, b, c⟩
    rcases d with ⟨d, hd⟩
    rw [show hexagonalPairOrbitFrom
      (x, Sum.inl (⟨d, hd⟩, b, c)) =
        s((x, b), (x + d, c)) by rfl]
    rw [hexagonalPairOrbitTo_mk]
    unfold hexagonalPairNormal
    simp only [add_sub_cancel_left, hd, dite_true]
  · rcases s with ⟨⟨b, c⟩, hbc⟩
    rw [show hexagonalPairOrbitFrom
      (x, Sum.inr ⟨(b, c), hbc⟩) = s((x, b), (x, c)) by rfl]
    rw [hexagonalPairOrbitTo_mk]
    unfold hexagonalPairNormal
    simp only [sub_self]
    have hn : ¬ siteLexPositive (0 : Site 2) := by
      simp [siteLexPositive]
    simp only [hn, dite_false, hbc, dite_true]


def hexagonalPairOrbitEquiv :
    Sym2 HexVertex ≃ Site 2 × HexagonalPairShape where
  toFun := hexagonalPairOrbitTo
  invFun := hexagonalPairOrbitFrom
  left_inv := hexagonalPairOrbitFrom_to
  right_inv := hexagonalPairOrbitTo_from

theorem hexagonalPairNormal_add (z : Site 2) (u v : HexVertex) :
    hexagonalPairNormal (hexTranslate z u) (hexTranslate z v) =
      (hexagonalPairNormal u v).map (fun b => b + z) id := by
  rcases u with ⟨x, b⟩
  rcases v with ⟨y, c⟩
  unfold hexagonalPairNormal
  simp only [hexTranslate_apply]
  have hsub : y + z - (x + z) = y - x := by abel
  have hsub' : x + z - (y + z) = x - y := by abel
  simp only [hsub, hsub']
  split_ifs <;> rfl

theorem hexagonalPairOrbitEquiv_add (z : Site 2) (e : Sym2 HexVertex) :
    hexagonalPairOrbitEquiv (Sym2.map (hexTranslate z) e) =
      (hexagonalPairOrbitEquiv e).map (fun b => b + z) id := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [hexagonalPairOrbitEquiv, Equiv.coe_fn_mk,
        Sym2.map_mk, hexagonalPairOrbitTo_mk]
      exact hexagonalPairNormal_add z u v




def triangularEdgePairShape (i : Fin 3) : TriangularPairShape :=
  (triangularPairNormal 0 (triangularStep i)).2


def triangularEdgePairBase (i : Fin 3) : Site 2 :=
  (triangularPairNormal 0 (triangularStep i)).1


def hexagonalEdgePairShape (i : Fin 3) : HexagonalPairShape :=
  (hexagonalPairNormal (0, false) (hexagonalStep i, true)).2

theorem triangularEdgePairShape_injective :
    Function.Injective triangularEdgePairShape := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [triangularEdgePairShape, triangularPairNormal,
      triangularStep, siteLexNonnegative] at hij ⊢
  all_goals
    have h := congrArg (fun s : TriangularPairShape => (s.1 0, s.1 1)) hij
    norm_num at h

theorem hexagonalEdgePairShape_injective :
    Function.Injective hexagonalEdgePairShape := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hexagonalEdgePairShape, hexagonalPairNormal,
      hexagonalStep, siteLexPositive, boolOrdered] at hij ⊢
  all_goals
    have h := congrArg (fun s : HexagonalPairShape =>
      match s with
      | Sum.inl d => (d.1.1 0, d.1.1 1)
      | Sum.inr _ => (0, 0)) hij
    norm_num at h

def IsTriangularEdgePairShape (s : TriangularPairShape) : Prop :=
  ∃ i, triangularEdgePairShape i = s

def IsHexagonalEdgePairShape (s : HexagonalPairShape) : Prop :=
  ∃ i, hexagonalEdgePairShape i = s

instance (s : TriangularPairShape) :
    Decidable (IsTriangularEdgePairShape s) := by
  unfold IsTriangularEdgePairShape
  infer_instance

instance (s : HexagonalPairShape) :
    Decidable (IsHexagonalEdgePairShape s) := by
  unfold IsHexagonalEdgePairShape
  infer_instance

noncomputable def triangularEdgePairShapeEquiv :
    Fin 3 ≃ {s : TriangularPairShape // IsTriangularEdgePairShape s} :=
  Equiv.ofBijective
    (fun i => ⟨triangularEdgePairShape i, ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => triangularEdgePairShape_injective
        (congrArg Subtype.val h),
      fun s => by
        rcases s with ⟨s, i, hi⟩
        exact ⟨i, Subtype.ext hi⟩⟩

noncomputable def hexagonalEdgePairShapeEquiv :
    Fin 3 ≃ {s : HexagonalPairShape // IsHexagonalEdgePairShape s} :=
  Equiv.ofBijective
    (fun i => ⟨hexagonalEdgePairShape i, ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => hexagonalEdgePairShape_injective
        (congrArg Subtype.val h),
      fun s => by
        rcases s with ⟨s, i, hi⟩
        exact ⟨i, Subtype.ext hi⟩⟩

private def longPairDisplacement (n : Nat) : Site 2 :=
  ![(n : Int) + 2, 0]

private theorem longPairDisplacement_nonnegative (n : Nat) :
    siteLexNonnegative (longPairDisplacement n) := by
  left
  simp only [longPairDisplacement, Matrix.cons_val_zero]
  exact add_pos_of_nonneg_of_pos (Int.natCast_nonneg n) (by norm_num)

private def triangularNonedgePairShape (n : Nat) : TriangularPairShape :=
  ⟨longPairDisplacement n, longPairDisplacement_nonnegative n⟩

private theorem triangularNonedgePairShape_not_edge (n : Nat) :
    ¬ IsTriangularEdgePairShape (triangularNonedgePairShape n) := by
  rintro ⟨i, hi⟩
  fin_cases i <;>
    have h0 := congrArg (fun s : TriangularPairShape => s.1 0) hi <;>
    simp [triangularNonedgePairShape, longPairDisplacement,
      triangularEdgePairShape, triangularPairNormal,
      triangularStep, siteLexNonnegative] at h0
  all_goals have hn : (0 : Int) <= n := Int.natCast_nonneg n
  all_goals omega

private theorem triangularNonedgePairShape_injective :
    Function.Injective triangularNonedgePairShape := by
  intro n m h
  have h0 := congrArg (fun s : TriangularPairShape => s.1 0) h
  simp [triangularNonedgePairShape, longPairDisplacement] at h0
  omega

private def triangularNonedgePairShapeEmbedding :
    Nat ↪ {s : TriangularPairShape // ¬ IsTriangularEdgePairShape s} where
  toFun n := ⟨triangularNonedgePairShape n,
    triangularNonedgePairShape_not_edge n⟩
  inj' _ _ h := triangularNonedgePairShape_injective
    (congrArg Subtype.val h)

private def hexagonalNonedgePairShape (n : Nat) : HexagonalPairShape :=
  Sum.inl (⟨longPairDisplacement n, by
    left
    simp only [longPairDisplacement, Matrix.cons_val_zero]
    exact add_pos_of_nonneg_of_pos (Int.natCast_nonneg n) (by norm_num)⟩,
      false, false)

private theorem hexagonalNonedgePairShape_not_edge (n : Nat) :
    ¬ IsHexagonalEdgePairShape (hexagonalNonedgePairShape n) := by
  rintro ⟨i, hi⟩
  have hc := congrArg (fun s : HexagonalPairShape =>
    match s with
    | Sum.inl d => d.2.2
    | Sum.inr _ => false) hi
  fin_cases i <;>
    simp [hexagonalNonedgePairShape, hexagonalEdgePairShape,
      hexagonalPairNormal, hexagonalStep, siteLexPositive,
      boolOrdered] at hc

private theorem hexagonalNonedgePairShape_injective :
    Function.Injective hexagonalNonedgePairShape := by
  intro n m h
  have h0 := congrArg (fun s : HexagonalPairShape =>
    match s with
    | Sum.inl d => d.1.1 0
    | Sum.inr _ => 0) h
  simp [hexagonalNonedgePairShape, longPairDisplacement] at h0
  omega

private def hexagonalNonedgePairShapeEmbedding :
    Nat ↪ {s : HexagonalPairShape // ¬ IsHexagonalEdgePairShape s} where
  toFun n := ⟨hexagonalNonedgePairShape n,
    hexagonalNonedgePairShape_not_edge n⟩
  inj' _ _ h := hexagonalNonedgePairShape_injective
    (congrArg Subtype.val h)

noncomputable def triHexNonedgePairShapeEquiv :
    {s : TriangularPairShape // ¬ IsTriangularEdgePairShape s} ≃
      {s : HexagonalPairShape // ¬ IsHexagonalEdgePairShape s} := by
  letI : Infinite
      {s : TriangularPairShape // ¬ IsTriangularEdgePairShape s} :=
    Infinite.of_injective _ triangularNonedgePairShapeEmbedding.injective
  letI : Infinite
      {s : HexagonalPairShape // ¬ IsHexagonalEdgePairShape s} :=
    Infinite.of_injective _ hexagonalNonedgePairShapeEmbedding.injective
  exact Classical.choice inferInstance



noncomputable def triHexPairShapeEquiv :
    TriangularPairShape ≃ HexagonalPairShape :=
  (Equiv.sumCompl IsTriangularEdgePairShape).symm |>.trans
    (((triangularEdgePairShapeEquiv.symm.trans
        hexagonalEdgePairShapeEquiv).sumCongr
      triHexNonedgePairShapeEquiv).trans
    (Equiv.sumCompl IsHexagonalEdgePairShape))

theorem triHexPairShapeEquiv_edge (i : Fin 3) :
    triHexPairShapeEquiv (triangularEdgePairShape i) =
      hexagonalEdgePairShape i := by
  unfold triHexPairShapeEquiv
  simp only [Equiv.trans_apply]
  rw [Equiv.sumCompl_symm_apply_of_pos ⟨i, rfl⟩]
  change (Equiv.sumCompl IsHexagonalEdgePairShape)
    (Sum.inl (hexagonalEdgePairShapeEquiv
      (triangularEdgePairShapeEquiv.symm
        ⟨triangularEdgePairShape i, ⟨i, rfl⟩⟩))) = _
  rw [show (⟨triangularEdgePairShape i, ⟨i, rfl⟩⟩ :
      {s : TriangularPairShape // IsTriangularEdgePairShape s}) =
        triangularEdgePairShapeEquiv i by rfl]
  simp [hexagonalEdgePairShapeEquiv]


def triHexPairShapeOffset (s : TriangularPairShape) : Site 2 :=
  if s = triangularEdgePairShape 2 then ![0, -1] else 0

theorem triHexPairShapeOffset_edge (i : Fin 3) :
    triangularEdgePairBase i + triHexPairShapeOffset
      (triangularEdgePairShape i) =
        (triHexIndexEquiv (0, i)).1 := by
  fin_cases i <;>
    simp [triangularEdgePairBase, triangularEdgePairShape,
      triangularPairNormal, triangularStep, siteLexNonnegative,
      triHexPairShapeOffset, triHexIndexEquiv, funext_iff]
  all_goals
    intro h
    have h1 := congrArg (fun s : TriangularPairShape => s.1 1) h
    norm_num at h1


noncomputable def triHexPairOrbitDataEquiv :
    (Site 2 × TriangularPairShape) ≃
      (Site 2 × HexagonalPairShape) where
  toFun a := (a.1 + triHexPairShapeOffset a.2,
    triHexPairShapeEquiv a.2)
  invFun b :=
    (b.1 - triHexPairShapeOffset (triHexPairShapeEquiv.symm b.2),
      triHexPairShapeEquiv.symm b.2)
  left_inv a := by
    rcases a with ⟨x, s⟩
    simp
  right_inv b := by
    rcases b with ⟨x, s⟩
    simp


noncomputable def triHexFullDualEdgeEquiv :
    Sym2 (Site 2) ≃ Sym2 HexVertex :=
  triangularPairOrbitEquiv.trans
    (triHexPairOrbitDataEquiv.trans hexagonalPairOrbitEquiv.symm)

theorem triHexPairOrbitDataEquiv_add (z : Site 2)
    (a : Site 2 × TriangularPairShape) :
    triHexPairOrbitDataEquiv (a.map (fun b => b + z) id) =
      (triHexPairOrbitDataEquiv a).map (fun b => b + z) id := by
  rcases a with ⟨x, s⟩
  change ((x + z) + triHexPairShapeOffset s, _) =
    ((x + triHexPairShapeOffset s) + z, _)
  apply Prod.ext
  · abel
  · rfl

theorem triHexFullDualEdgeEquiv_shift (z : Site 2)
    (e : Sym2 (Site 2)) :
    triHexFullDualEdgeEquiv (Sym2.map (siteTranslate z) e) =
      Sym2.map (hexTranslate z) (triHexFullDualEdgeEquiv e) := by
  apply hexagonalPairOrbitEquiv.injective
  simp only [triHexFullDualEdgeEquiv, Equiv.trans_apply]
  rw [hexagonalPairOrbitEquiv_add, triangularPairOrbitEquiv_add,
    triHexPairOrbitDataEquiv_add]
  simp

theorem triangularPairOrbitEquiv_indexedEdge (a : TriHexEdgeIndex) :
    triangularPairOrbitEquiv (triangularIndexedEdge a) =
      (a.1 + triangularEdgePairBase a.2,
        triangularEdgePairShape a.2) := by
  rcases a with ⟨x, i⟩
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  fin_cases i <;>
    simp [triangularPairOrbitEquiv, triangularPairOrbitTo_mk,
      triangularIndexedEdge, triangularEdgePairBase,
      triangularEdgePairShape, triangularPairNormal,
      triangularStep, siteLexNonnegative, hxHead, hxTail]

theorem hexagonalPairOrbitEquiv_indexedEdge (a : TriHexEdgeIndex) :
    hexagonalPairOrbitEquiv (hexagonalIndexedEdge a) =
      (a.1, hexagonalEdgePairShape a.2) := by
  rcases a with ⟨x, i⟩
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  fin_cases i <;>
    simp [hexagonalPairOrbitEquiv, hexagonalPairOrbitTo_mk,
      hexagonalIndexedEdge, hexagonalEdgePairShape,
      hexagonalPairNormal, hexagonalStep, siteLexPositive,
      boolOrdered, hxHead, hxTail]



theorem triHexFullDualEdgeEquiv_indexedEdge (a : TriHexEdgeIndex) :
    triHexFullDualEdgeEquiv (triangularIndexedEdge a) =
      hexagonalIndexedEdge (triHexIndexEquiv a) := by
  apply hexagonalPairOrbitEquiv.injective
  simp only [triHexFullDualEdgeEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [triangularPairOrbitEquiv_indexedEdge,
    hexagonalPairOrbitEquiv_indexedEdge]
  change (a.1 + triangularEdgePairBase a.2 +
      triHexPairShapeOffset (triangularEdgePairShape a.2),
        triHexPairShapeEquiv (triangularEdgePairShape a.2)) = _
  rw [triHexPairShapeEquiv_edge]
  apply Prod.ext
  · change a.1 + triangularEdgePairBase a.2 +
      triHexPairShapeOffset (triangularEdgePairShape a.2) =
        (triHexIndexEquiv a).1
    rw [add_assoc, triHexPairShapeOffset_edge]
    have h := congrArg Prod.fst (triHexIndexEquiv_add a.1 (0, a.2))
    simpa [add_comm] using h.symm
  · change hexagonalEdgePairShape a.2 =
      hexagonalEdgePairShape (triHexIndexEquiv a).2
    rcases a with ⟨x, i⟩
    fin_cases i <;> rfl

theorem triHexFullDualEdgeEquiv_edgeChart (a : TriHexEdgeIndex) :
    triHexFullDualEdgeEquiv (triangularEdgeChart a : Sym2 (Site 2)) =
      (triHexDualEdgeEquiv (triangularEdgeChart a) : Sym2 HexVertex) := by
  rw [triHexDualEdgeEquiv_chart]
  exact triHexFullDualEdgeEquiv_indexedEdge a

theorem triHexFullDualEdgeEquiv_mem_edgeSet (e : Sym2 (Site 2)) :
    e ∈ triangularGraph.edgeSet ↔
      triHexFullDualEdgeEquiv e ∈ hexagonalGraph.edgeSet := by
  constructor
  · intro he
    let et : triangularGraph.edgeSet := ⟨e, he⟩
    obtain ⟨a, ha⟩ := triangularEdgeChart_surjective et
    have hval : triangularIndexedEdge a = e :=
      congrArg Subtype.val ha
    rw [← hval, triHexFullDualEdgeEquiv_indexedEdge]
    exact hexagonalIndexedEdge_mem (triHexIndexEquiv a)
  · intro he
    let ft : hexagonalGraph.edgeSet :=
      ⟨triHexFullDualEdgeEquiv e, he⟩
    obtain ⟨b, hb⟩ := hexagonalEdgeChart_surjective ft
    let a := triHexIndexEquiv.symm b
    have hbval : hexagonalIndexedEdge b = triHexFullDualEdgeEquiv e :=
      congrArg Subtype.val hb
    have hpair : triHexFullDualEdgeEquiv (triangularIndexedEdge a) =
        triHexFullDualEdgeEquiv e := by
      rw [triHexFullDualEdgeEquiv_indexedEdge]
      simpa [a] using hbval
    have ha : triangularIndexedEdge a = e :=
      triHexFullDualEdgeEquiv.injective hpair
    rw [← ha]
    exact triangularIndexedEdge_mem a

theorem triHexFullDualEdgeEquiv_eq_edgeDual
    (e : triangularGraph.edgeSet) :
    triHexFullDualEdgeEquiv (e : Sym2 (Site 2)) =
      (triHexDualEdgeEquiv e : Sym2 HexVertex) := by
  let a := triangularEdgeChartEquiv.symm e
  have ha : triangularEdgeChart a = e :=
    triangularEdgeChartEquiv.apply_symm_apply e
  rw [← ha]
  exact triHexFullDualEdgeEquiv_edgeChart a

end StatMech.FK.PeriodicPlanar
