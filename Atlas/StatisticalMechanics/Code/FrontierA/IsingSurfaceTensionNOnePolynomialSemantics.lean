/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
import Code.FrontierA.IsingSurfaceTensionNOneLayerCode
import Std.Data.TreeMap.Lemmas
import Std.Data.DTreeMap.Internal.Lemmas










open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl

namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

private theorem biExponentCompare_eq_compareLex :
    biExponentCompare =
      compareLex (compareOn (fun p : Int × Int => p.1))
        (compareOn (fun p : Int × Int => p.2)) := by
  rfl

private local instance : TransCmp biExponentCompare := by
  rw [biExponentCompare_eq_compareLex]
  infer_instance

private local instance : LawfulEqCmp biExponentCompare := by
  refine { eq_of_compare := ?_ }
  intro a b h
  simp only [biExponentCompare_eq_compareLex, compareLex_eq_eq,
    compareOn, LawfulEqCmp.compare_eq_iff_eq] at h
  exact Prod.ext h.1 h.2

noncomputable def BiTerm.eval (X Y : Real) (t : BiTerm) : Real :=
  (t.coeff : Real) * X ^ t.ex * Y ^ t.ey

noncomputable def BiPoly.eval (X Y : Real) (p : BiPoly) : Real :=
  (p.terms.map (BiTerm.eval X Y)).sum

private noncomputable def termMapEval (X Y : Real) (m : BiTermMap) : Real :=
  (m.toList.map fun t =>
    (t.2 : Real) * X ^ t.1.1 * Y ^ t.1.2).sum

private def addCoefficientOption (d : Int) : Option Int -> Option Int
  | none => if d = 0 then none else some d
  | some c => if c + d = 0 then none else some (c + d)

private def addTermToMap (m : BiTermMap) (t : BiTerm) : BiTermMap :=
  m.alter (t.ex, t.ey) (addCoefficientOption t.coeff)

private noncomputable def modelEntryEval (X Y : Real)
    (e : (k : Int × Int) × (fun _ => Int) k) : Real :=
  (e.2 : Real) * X ^ e.1.1 * Y ^ e.1.2

private theorem toList_alter_perm (m : BiTermMap) (k : Int × Int)
    (f : Option Int -> Option Int) :
    (m.alter k f).toList.Perm
      ((Std.Internal.List.Const.alterKey k f
        m.inner.inner.toListModel).map fun e => (e.1, e.2)) := by
  letI : Ord (Int × Int) := ⟨biExponentCompare⟩
  letI : TransOrd (Int × Int) :=
    inferInstanceAs (TransCmp biExponentCompare)
  letI : LawfulEqOrd (Int × Int) :=
    inferInstanceAs (LawfulEqCmp biExponentCompare)
  letI : LawfulBEqOrd (Int × Int) := by infer_instance
  have h := Std.DTreeMap.Internal.Impl.Const.toListModel_alter
      (t := m.inner.inner) (a := k) (f := f)
      m.inner.wf.balanced m.inner.wf.ordered
  have hm := h.map (fun e => (e.1, e.2))
  simpa only [TreeMap.alter, TreeMap.toList, DTreeMap.Const.alter,
    DTreeMap.Const.toList,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map,
    List.map_map, Function.comp_apply] using hm

private theorem sum_modelEntryEval_alterKey_addCoefficientOption
    (X Y : Real) (k : Int × Int) (d : Int)
    (l : List ((k : Int × Int) × (fun _ => Int) k))
    (hl : Std.Internal.List.DistinctKeys l) :
    ((Std.Internal.List.Const.alterKey k (addCoefficientOption d) l).map
        (modelEntryEval X Y)).sum =
      (l.map (modelEntryEval X Y)).sum +
        (d : Real) * X ^ k.1 * Y ^ k.2 := by
  induction l with
  | nil =>
      by_cases hd : d = 0
      · simp [Std.Internal.List.Const.alterKey_nil,
          addCoefficientOption, hd]
      · simp [Std.Internal.List.Const.alterKey_nil,
          addCoefficientOption, hd, modelEntryEval]
  | cons e l ih =>
      rcases e with ⟨ek, ec⟩
      rw [Std.Internal.List.distinctKeys_cons_iff] at hl
      have hp := Std.Internal.List.Const.alterKey_cons_perm
        (k := k) (f := addCoefficientOption d) (k' := ek)
        (v' := ec) (l := l)
      have hs := (hp.map (modelEntryEval X Y)).sum_eq
      rw [hs]
      by_cases hek : ek == k
      · simp only [hek, ↓reduceIte]
        have heq : ek = k := eq_of_beq hek
        subst ek
        by_cases hz : ec + d = 0
        · simp only [addCoefficientOption, hz, ↓reduceIte, List.map,
            List.sum_cons, modelEntryEval]
          have hzR : (ec : Real) + (d : Real) = 0 := by
            exact_mod_cast hz
          symm
          calc
            (ec : Real) * X ^ k.1 * Y ^ k.2 +
                (l.map (modelEntryEval X Y)).sum +
                (d : Real) * X ^ k.1 * Y ^ k.2 =
              (l.map (modelEntryEval X Y)).sum +
                ((ec : Real) + (d : Real)) *
                  (X ^ k.1 * Y ^ k.2) := by ring
            _ = (l.map (modelEntryEval X Y)).sum := by rw [hzR]; ring
        · simp only [addCoefficientOption, hz, ↓reduceIte, List.map,
            List.sum_cons, modelEntryEval]
          push_cast
          ring
      · simp only [hek, Bool.false_eq_true, ↓reduceIte, List.map,
          List.sum_cons, modelEntryEval]
        rw [ih hl.1]
        ring


private theorem termMapEval_addTermToMap
    (X Y : Real) (m : BiTermMap) (t : BiTerm) :
    termMapEval X Y (addTermToMap m t) =
      termMapEval X Y m + t.eval X Y := by
  letI : Ord (Int × Int) := ⟨biExponentCompare⟩
  letI : TransOrd (Int × Int) :=
    inferInstanceAs (TransCmp biExponentCompare)
  letI : LawfulEqOrd (Int × Int) :=
    inferInstanceAs (LawfulEqCmp biExponentCompare)
  letI : LawfulBEqOrd (Int × Int) := by infer_instance
  unfold termMapEval addTermToMap BiTerm.eval
  have hp := toList_alter_perm m (t.ex, t.ey)
    (addCoefficientOption t.coeff)
  rw [(hp.map fun e =>
    (e.2 : Real) * X ^ e.1.1 * Y ^ e.1.2).sum_eq]
  simpa only [TreeMap.toList, DTreeMap.Const.toList,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map,
    List.map_map, Function.comp_apply, modelEntryEval] using
    sum_modelEntryEval_alterKey_addCoefficientOption X Y (t.ex, t.ey)
      t.coeff m.inner.inner.toListModel m.inner.wf.ordered.distinctKeys

private theorem termMapEval_foldl_addTermToMap
    (X Y : Real) (m : BiTermMap) (ts : List BiTerm) :
    termMapEval X Y (ts.foldl addTermToMap m) =
      termMapEval X Y m + (ts.map (BiTerm.eval X Y)).sum := by
  induction ts generalizing m with
  | nil => simp
  | cons t ts ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, termMapEval_addTermToMap]
      ring

theorem BiPoly.eval_ofTerms (X Y : Real) (ts : List BiTerm) :
    BiPoly.eval X Y (BiPoly.ofTerms ts) =
      (ts.map (BiTerm.eval X Y)).sum := by
  rw [BiPoly.ofTerms]
  unfold BiPoly.eval
  simp only [List.map_map]
  change termMapEval X Y
      (ts.foldl addTermToMap (TreeMap.empty : BiTermMap)) = _
  rw [termMapEval_foldl_addTermToMap]
  have hempty : termMapEval X Y (TreeMap.empty : BiTermMap) = 0 := by
    unfold termMapEval TreeMap.empty TreeMap.toList DTreeMap.Const.toList
    rfl
  rw [hempty, zero_add]

@[simp] theorem BiPoly.eval_monomial (X Y : Real) (ex ey coeff : Int) :
    BiPoly.eval X Y (.monomial ex ey coeff) =
      (coeff : Real) * X ^ ex * Y ^ ey := by
  rw [BiPoly.monomial, BiPoly.eval_ofTerms]
  simp [BiTerm.eval]

@[simp] theorem BiPoly.eval_add (X Y : Real) (p q : BiPoly) :
    BiPoly.eval X Y (p + q) = p.eval X Y + q.eval X Y := by
  change BiPoly.eval X Y (BiPoly.add p q) = _
  rw [BiPoly.add, BiPoly.eval_ofTerms]
  simp [BiPoly.eval]

@[simp] theorem BiPoly.eval_neg (X Y : Real) (p : BiPoly) :
    BiPoly.eval X Y (-p) = -p.eval X Y := by
  change BiPoly.eval X Y (BiPoly.neg p) = _
  rw [BiPoly.neg, BiPoly.eval_ofTerms]
  unfold BiPoly.eval
  induction p.terms with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_map, List.map_cons, List.sum_cons,
        ] at ih ⊢
      unfold BiTerm.eval at ih ⊢
      push_cast
      rw [ih]
      ring

@[simp] theorem BiPoly.eval_sub (X Y : Real) (p q : BiPoly) :
    BiPoly.eval X Y (p - q) = p.eval X Y - q.eval X Y := by
  change BiPoly.eval X Y (BiPoly.sub p q) = _
  rw [BiPoly.sub]
  change BiPoly.eval X Y (p + (-q)) = _
  rw [BiPoly.eval_add, BiPoly.eval_neg]
  rfl

private theorem sum_termProduct_right
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (s : BiTerm) (ts : List BiTerm) :
    (((ts.map fun t =>
        { ex := s.ex + t.ex, ey := s.ey + t.ey,
          coeff := s.coeff * t.coeff }).map (BiTerm.eval X Y)).sum) =
      s.eval X Y * (ts.map (BiTerm.eval X Y)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      unfold BiTerm.eval
      simp only [Int.cast_mul, zpow_add₀ hX, zpow_add₀ hY]
      ring

private theorem sum_termProducts
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (ss ts : List BiTerm) :
    ((ss.flatMap fun s => ts.map fun t =>
        { ex := s.ex + t.ex, ey := s.ey + t.ey,
          coeff := s.coeff * t.coeff }).map (BiTerm.eval X Y)).sum =
      (ss.map (BiTerm.eval X Y)).sum *
        (ts.map (BiTerm.eval X Y)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ih]
      rw [sum_termProduct_right X Y hX hY]
      ring

@[simp] theorem BiPoly.eval_mul (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (p q : BiPoly) :
    BiPoly.eval X Y (p * q) = p.eval X Y * q.eval X Y := by
  change BiPoly.eval X Y (BiPoly.mul p q) = _
  rw [BiPoly.mul, BiPoly.eval_ofTerms]
  exact sum_termProducts X Y hX hY p.terms q.terms

theorem BiPoly.eval_mapExponent (X Y : Real)
    (f : Int -> Int -> Int × Int) (p : BiPoly) :
    (p.mapExponent f).eval X Y =
      (p.terms.map fun t =>
        (t.coeff : Real) * X ^ (f t.ex t.ey).1 *
          Y ^ (f t.ex t.ey).2).sum := by
  rw [BiPoly.mapExponent, BiPoly.eval_ofTerms]
  simp only [List.map_map]
  congr 1

theorem BiPoly.eval_flipY (X Y : Real) (p : BiPoly) :
    (p.mapExponent fun ex ey => (ex, -ey)).eval X Y =
      p.eval X Y⁻¹ := by
  rw [BiPoly.eval_mapExponent]
  unfold BiPoly.eval
  congr 1
  apply List.map_congr_left
  intro t ht
  unfold BiTerm.eval
  rw [inv_zpow]
  rw [zpow_neg]

theorem BiPoly.eval_scaleObservable (X Y : Real) (p : BiPoly)
    (power : Nat) :
    (p.scaleObservable power).eval X Y =
      (p.terms.map fun t =>
        ((t.coeff * (2 * t.ey - 9) ^ power : Int) : Real) *
          X ^ t.ex * Y ^ t.ey).sum := by
  rw [BiPoly.scaleObservable, BiPoly.eval_ofTerms]
  simp only [List.map_map]
  congr 1

private noncomputable def evalYSquareDivisionInvariant (X Y : Real)
    (qr : BiPoly × BiPoly) : Real :=
  qr.1.eval X Y * (Y ^ 2 - 1) + qr.2.eval X Y

private theorem evalYSquareDivisionInvariant_step
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (e : Int) (qr : BiPoly × BiPoly) :
    evalYSquareDivisionInvariant X Y
        (BiPoly.divYsqSubOneStep e qr) =
      evalYSquareDivisionInvariant X Y qr := by
  rcases qr with ⟨q, r⟩
  unfold BiPoly.divYsqSubOneStep evalYSquareDivisionInvariant
  dsimp only
  let qadd := (r.leadingY e).mapExponent fun ex ey => (ex, ey - 2)
  let factor : BiPoly := .ofTerms
    [{ ex := 0, ey := 2, coeff := 1 },
      { ex := 0, ey := 0, coeff := -1 }]
  change (q.add qadd).eval X Y * (Y ^ 2 - 1) +
      (r.sub (qadd.mul factor)).eval X Y =
    q.eval X Y * (Y ^ 2 - 1) + r.eval X Y
  have ha := BiPoly.eval_add X Y q qadd
  change (q.add qadd).eval X Y = q.eval X Y + qadd.eval X Y at ha
  have hs := BiPoly.eval_sub X Y r (qadd.mul factor)
  change (r.sub (qadd.mul factor)).eval X Y =
    r.eval X Y - (qadd.mul factor).eval X Y at hs
  have hm := BiPoly.eval_mul X Y hX hY qadd factor
  change (qadd.mul factor).eval X Y =
    qadd.eval X Y * factor.eval X Y at hm
  have hf : factor.eval X Y = Y ^ 2 - 1 := by
    unfold factor
    rw [BiPoly.eval_ofTerms]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      BiTerm.eval]
    norm_num
    rfl
  rw [ha, hs, hm, hf]
  ring

private theorem evalYSquareDivisionInvariant_foldl
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (es : List Int) (qr : BiPoly × BiPoly) :
    evalYSquareDivisionInvariant X Y
        (es.foldl (fun qr e => BiPoly.divYsqSubOneStep e qr) qr) =
      evalYSquareDivisionInvariant X Y qr := by
  induction es generalizing qr with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldl_cons, ih,
        evalYSquareDivisionInvariant_step X Y hX hY]

theorem BiPoly.eval_divYsqSubOne
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (top : Nat) (p : BiPoly) :
    p.eval X Y =
      (p.divYsqSubOne top).1.eval X Y * (Y ^ 2 - 1) +
        (p.divYsqSubOne top).2.eval X Y := by
  have h := evalYSquareDivisionInvariant_foldl X Y hX hY
    (descendingFrom top) (.monomial 0 0 0, p)
  unfold BiPoly.divYsqSubOne
  simpa [evalYSquareDivisionInvariant] using h.symm

private noncomputable def evalXSquareDivisionInvariant (X Y : Real)
    (qr : BiPoly × BiPoly) : Real :=
  qr.1.eval X Y * (X ^ 2 - 1) + qr.2.eval X Y

private theorem evalXSquareDivisionInvariant_step
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (e : Int) (qr : BiPoly × BiPoly) :
    evalXSquareDivisionInvariant X Y
        (BiPoly.divXsqSubOneStep e qr) =
      evalXSquareDivisionInvariant X Y qr := by
  rcases qr with ⟨q, r⟩
  unfold BiPoly.divXsqSubOneStep evalXSquareDivisionInvariant
  dsimp only
  let qadd := (r.leadingX e).mapExponent fun ex ey => (ex - 2, ey)
  let factor : BiPoly := .ofTerms
    [{ ex := 2, ey := 0, coeff := 1 },
      { ex := 0, ey := 0, coeff := -1 }]
  change (q.add qadd).eval X Y * (X ^ 2 - 1) +
      (r.sub (qadd.mul factor)).eval X Y =
    q.eval X Y * (X ^ 2 - 1) + r.eval X Y
  have ha := BiPoly.eval_add X Y q qadd
  change (q.add qadd).eval X Y = q.eval X Y + qadd.eval X Y at ha
  have hs := BiPoly.eval_sub X Y r (qadd.mul factor)
  change (r.sub (qadd.mul factor)).eval X Y =
    r.eval X Y - (qadd.mul factor).eval X Y at hs
  have hm := BiPoly.eval_mul X Y hX hY qadd factor
  change (qadd.mul factor).eval X Y =
    qadd.eval X Y * factor.eval X Y at hm
  have hf : factor.eval X Y = X ^ 2 - 1 := by
    unfold factor
    rw [BiPoly.eval_ofTerms]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      BiTerm.eval]
    norm_num
    rfl
  rw [ha, hs, hm, hf]
  ring

private theorem evalXSquareDivisionInvariant_foldl
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (es : List Int) (qr : BiPoly × BiPoly) :
    evalXSquareDivisionInvariant X Y
        (es.foldl (fun qr e => BiPoly.divXsqSubOneStep e qr) qr) =
      evalXSquareDivisionInvariant X Y qr := by
  induction es generalizing qr with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldl_cons, ih,
        evalXSquareDivisionInvariant_step X Y hX hY]

theorem BiPoly.eval_divXsqSubOne
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (top : Nat) (p : BiPoly) :
    p.eval X Y =
      (p.divXsqSubOne top).1.eval X Y * (X ^ 2 - 1) +
        (p.divXsqSubOne top).2.eval X Y := by
  have h := evalXSquareDivisionInvariant_foldl X Y hX hY
    (descendingFrom top) (.monomial 0 0 0, p)
  unfold BiPoly.divXsqSubOne
  simpa [evalXSquareDivisionInvariant] using h.symm

theorem BiPoly.eval_eq_zero_of_isEmpty (X Y : Real) (p : BiPoly)
    (h : p.terms.isEmpty = true) :
    p.eval X Y = 0 := by
  have hp : p.terms = [] := by simpa using h
  unfold BiPoly.eval
  rw [hp]
  rfl

theorem eval_clearedSkewPolyOf_eq_factors_of_remainderCertificate
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hcert : remainderCertificateOf p = true) :
    (clearedSkewPolyOf p).eval X Y =
      (quotientPolyOf p).eval X Y * (X ^ 2 - 1) * (Y ^ 2 - 1) := by
  let c := clearedSkewPolyOf p
  let yd := c.divYsqSubOne 34
  let xd := yd.1.divXsqSubOne 294
  unfold remainderCertificateOf at hcert
  have hrem := Bool.and_eq_true_iff.mp hcert
  have hry0 : (quotientRemainderYOf p).eval X Y = 0 :=
    BiPoly.eval_eq_zero_of_isEmpty X Y (quotientRemainderYOf p) hrem.1
  have hrx0 : (quotientRemainderXOf p).eval X Y = 0 :=
    BiPoly.eval_eq_zero_of_isEmpty X Y (quotientRemainderXOf p) hrem.2
  have hry : yd.2.eval X Y = 0 := by
    simpa only [quotientRemainderYOf, yd, c] using hry0
  have hrx : xd.2.eval X Y = 0 := by
    simpa only [quotientRemainderXOf, xd, yd, c] using hrx0
  have hy := BiPoly.eval_divYsqSubOne X Y hX hY 34 c
  have hx := BiPoly.eval_divXsqSubOne X Y hX hY 294 yd.1
  change c.eval X Y = yd.1.eval X Y * (Y ^ 2 - 1) +
    yd.2.eval X Y at hy
  change yd.1.eval X Y = xd.1.eval X Y * (X ^ 2 - 1) +
    xd.2.eval X Y at hx
  change c.eval X Y = xd.1.eval X Y * (X ^ 2 - 1) *
    (Y ^ 2 - 1)
  rw [hy, hry, add_zero, hx, hrx, add_zero]

private theorem binomialListSum (C : Real) (n : Nat) :
    ((List.range (n + 1)).map fun a =>
      ((n.choose a : Nat) : Real) * C ^ a).sum = (1 + C) ^ n := by
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  calc
    (∑ x ∈ Finset.range (n + 1), (n.choose x : Real) * C ^ x) =
        ∑ x ∈ Finset.range (n + 1),
          C ^ x * 1 ^ (n - x) * (n.choose x : Real) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (C + 1) ^ n := (add_pow C 1 n).symm
    _ = (1 + C) ^ n := by rw [add_comm]

private def shiftedTermExpansion (t : BiTerm) : List BiTerm :=
  (List.range (Int.toNat t.ex + 1)).flatMap fun (a : Nat) =>
      (List.range (Int.toNat t.ey + 1)).map fun (b : Nat) =>
        { ex := (a : Int), ey := (b : Int),
          coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
            ((Int.toNat t.ey).choose b : Int) }

private theorem shiftedTermListSum (C D : Real) (t : BiTerm) :
    ((shiftedTermExpansion t).map (BiTerm.eval C D)).sum =
      (t.coeff : Real) * (1 + C) ^ Int.toNat t.ex *
        (1 + D) ^ Int.toNat t.ey := by
  unfold shiftedTermExpansion
  have hinner (a : Nat) :
      (((List.range (Int.toNat t.ey + 1)).map fun b =>
        { ex := (a : Int), ey := (b : Int),
          coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
            ((Int.toNat t.ey).choose b : Int) }).map
          (BiTerm.eval C D)).sum =
        (t.coeff : Real) * (Int.toNat t.ex).choose a * C ^ a *
          (1 + D) ^ Int.toNat t.ey := by
    rw [← binomialListSum D (Int.toNat t.ey)]
    have hbs (bs : List Nat) :
        ((bs.map fun b =>
          { ex := (a : Int), ey := (b : Int),
            coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
              ((Int.toNat t.ey).choose b : Int) }).map
            (BiTerm.eval C D)).sum =
          (t.coeff : Real) * (Int.toNat t.ex).choose a * C ^ a *
            ((bs.map fun b =>
              ((Int.toNat t.ey).choose b : Real) * D ^ b).sum) := by
      induction bs with
      | nil => simp
      | cons b bs ih =>
          simp only [List.map_cons, List.sum_cons] at ih ⊢
          rw [ih]
          unfold BiTerm.eval
          simp only [Int.cast_mul, Int.cast_natCast, zpow_natCast]
          ring
    exact hbs (List.range (Int.toNat t.ey + 1))
  have houter (as : List Nat) :
      ((as.flatMap fun a =>
        (List.range (Int.toNat t.ey + 1)).map fun b =>
          { ex := (a : Int), ey := (b : Int),
            coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
              ((Int.toNat t.ey).choose b : Int) }).map
          (BiTerm.eval C D)).sum =
        (t.coeff : Real) *
          ((as.map fun a =>
            ((Int.toNat t.ex).choose a : Real) * C ^ a).sum) *
          (1 + D) ^ Int.toNat t.ey := by
    induction as with
    | nil => simp
    | cons a as ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons, hinner, ih]
        ring
  rw [houter]
  rw [binomialListSum]

theorem BiPoly.eval_shiftToOne
    (q : BiPoly) (C D : Real)
    (hexp : ∀ t ∈ q.terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey) :
    q.shiftToOne.eval C D = q.eval (1 + C) (1 + D) := by
  have hlist : ∀ qs : List BiTerm,
      (∀ t ∈ qs, 0 ≤ t.ex ∧ 0 ≤ t.ey) ->
      (((qs.flatMap shiftedTermExpansion).map (BiTerm.eval C D)).sum) =
        (qs.map (BiTerm.eval (1 + C) (1 + D))).sum := by
    intro qs
    induction qs with
    | nil => intro hqs; simp
    | cons t ts ih =>
        intro hqs
        have ht := hqs t (by simp)
        have hts : ∀ s ∈ ts, 0 ≤ s.ex ∧ 0 ≤ s.ey := by
          intro s hs
          exact hqs s (by simp [hs])
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons]
        rw [shiftedTermListSum, ih hts]
        have hx : (1 + C) ^ Int.toNat t.ex = (1 + C) ^ t.ex := by
          rw [← zpow_natCast]
          rw [Int.toNat_of_nonneg ht.1]
        have hy : (1 + D) ^ Int.toNat t.ey = (1 + D) ^ t.ey := by
          rw [← zpow_natCast]
          rw [Int.toNat_of_nonneg ht.2]
        rw [hx, hy]
        rfl
  rw [BiPoly.shiftToOne, BiPoly.eval_ofTerms]
  unfold BiPoly.eval
  simpa only [shiftedTermExpansion] using
    hlist q.terms hexp

theorem BiPoly.eval_shiftedQuotientPolyOf
    (p : BiPoly) (C D : Real)
    (hexp : ∀ t ∈ (quotientPolyOf p).terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey) :
    (shiftedQuotientPolyOf p).eval C D =
      (quotientPolyOf p).eval (1 + C) (1 + D) := by
  exact BiPoly.eval_shiftToOne (quotientPolyOf p) C D hexp

theorem BiPoly.eval_nonneg_of_coeff_nonneg
    (p : BiPoly) (X Y : Real) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hcoeff : ∀ t ∈ p.terms, 0 ≤ t.coeff) :
    0 ≤ p.eval X Y := by
  unfold BiPoly.eval
  have hlist : ∀ ts : List BiTerm,
      (∀ t ∈ ts, 0 ≤ t.coeff) ->
      0 ≤ (ts.map (BiTerm.eval X Y)).sum := by
    intro ts
    induction ts with
    | nil => intro hts; simp
    | cons t ts ih =>
        intro hts
        simp only [List.map_cons, List.sum_cons]
        apply add_nonneg
        · unfold BiTerm.eval
          have hct : 0 ≤ t.coeff := hts t (by simp)
          have hc : (0 : Real) ≤ (t.coeff : Real) := by
            exact_mod_cast hct
          exact mul_nonneg
            (mul_nonneg hc (zpow_nonneg hX t.ex))
            (zpow_nonneg hY t.ey)
        · apply ih
          intro s hs
          exact hts s (by simp [hs])
  exact hlist p.terms hcoeff

theorem eval_shiftedQuotientPolyOf_nonneg_of_coefficientCertificate
    (p : BiPoly) (C D : Real) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcert : coefficientCertificateOf p = true) :
    0 ≤ (shiftedQuotientPolyOf p).eval C D := by
  unfold coefficientCertificateOf at hcert
  apply BiPoly.eval_nonneg_of_coeff_nonneg _ C D hC hD
  intro t ht
  have hall := List.all_eq_true.mp hcert
  have h := hall t ht
  simpa using h

theorem eval_quotientPolyOf_nonneg_of_coefficientCertificate
    (p : BiPoly) (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hexp : ∀ t ∈ (quotientPolyOf p).terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey)
    (hcert : coefficientCertificateOf p = true) :
    0 ≤ (quotientPolyOf p).eval X Y := by
  have hnonneg :=
    eval_shiftedQuotientPolyOf_nonneg_of_coefficientCertificate p
      (X - 1) (Y - 1) (sub_nonneg.mpr hX) (sub_nonneg.mpr hY) hcert
  rw [BiPoly.eval_shiftedQuotientPolyOf p (X - 1) (Y - 1) hexp]
    at hnonneg
  have hx : 1 + (X - 1) = X := by ring
  have hy : 1 + (Y - 1) = Y := by ring
  rw [hx, hy] at hnonneg
  exact hnonneg

theorem BiPoly.eval_mapExponent_add
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (ax ay : Int) :
    (p.mapExponent fun ex ey => (ex + ax, ey + ay)).eval X Y =
      p.eval X Y * X ^ ax * Y ^ ay := by
  rw [BiPoly.eval_mapExponent]
  unfold BiPoly.eval
  induction p.terms with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, zpow_add₀ hX, zpow_add₀ hY]
      unfold BiTerm.eval
      ring

theorem eval_clearedSkewPolyOf_eq_scaled_neg_skew
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0) :
    (clearedSkewPolyOf p).eval X Y =
      -(reflectedVarianceSkewPolyOf p).eval X Y * X ^ (-17 : Int) *
        Y ^ (17 : Int) := by
  unfold clearedSkewPolyOf
  change ((-(reflectedVarianceSkewPolyOf p)).mapExponent
    fun ex ey => (ex + (-17 : Int), ey + (17 : Int))).eval X Y = _
  rw [BiPoly.eval_mapExponent_add _ X Y hX hY, BiPoly.eval_neg]

theorem eval_clearedSkewPolyOf_nonneg_of_certificate
    (p : BiPoly) (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hexp : ∀ t ∈ (quotientPolyOf p).terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey)
    (hcert : certificateOf p = true) :
    0 ≤ (clearedSkewPolyOf p).eval X Y := by
  unfold certificateOf at hcert
  have hc := Bool.and_eq_true_iff.mp hcert
  have hX0 : X ≠ 0 := ne_of_gt (_root_.lt_of_lt_of_le zero_lt_one hX)
  have hY0 : Y ≠ 0 := ne_of_gt (_root_.lt_of_lt_of_le zero_lt_one hY)
  have hq := eval_quotientPolyOf_nonneg_of_coefficientCertificate
    p X Y hX hY hexp hc.2
  have hfactor :=
    eval_clearedSkewPolyOf_eq_factors_of_remainderCertificate
      p X Y hX0 hY0 hc.1
  rw [hfactor]
  have hxf : 0 ≤ X ^ 2 - 1 := by
    calc
      0 ≤ (X - 1) * (X + 1) := mul_nonneg (sub_nonneg.mpr hX)
        (add_nonneg (zero_le_one.trans hX) zero_le_one)
      _ = X ^ 2 - 1 := by ring
  have hyf : 0 ≤ Y ^ 2 - 1 := by
    calc
      0 ≤ (Y - 1) * (Y + 1) := mul_nonneg (sub_nonneg.mpr hY)
        (add_nonneg (zero_le_one.trans hY) zero_le_one)
      _ = Y ^ 2 - 1 := by ring
  exact mul_nonneg (mul_nonneg hq hxf) hyf

theorem eval_reflectedVarianceSkewPolyOf_nonpos_of_certificate
    (p : BiPoly) (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hexp : ∀ t ∈ (quotientPolyOf p).terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey)
    (hcert : certificateOf p = true) :
    (reflectedVarianceSkewPolyOf p).eval X Y ≤ 0 := by
  have hXpos : 0 < X := _root_.lt_of_lt_of_le zero_lt_one hX
  have hYpos : 0 < Y := _root_.lt_of_lt_of_le zero_lt_one hY
  have hc := eval_clearedSkewPolyOf_nonneg_of_certificate
    p X Y hX hY hexp hcert
  rw [eval_clearedSkewPolyOf_eq_scaled_neg_skew p X Y
    hXpos.ne' hYpos.ne'] at hc
  rw [mul_assoc] at hc
  have hscale : 0 < X ^ (-17 : Int) * Y ^ (17 : Int) :=
    mul_pos (zpow_pos hXpos _) (zpow_pos hYpos _)
  have hneg : 0 ≤ -(reflectedVarianceSkewPolyOf p).eval X Y :=
    (mul_nonneg_iff_of_pos_right hscale).mp hc
  linarith




theorem eval_reflectedVarianceSkewPolyOf_nonpos_of_explicit_factor
    (p q : BiPoly) (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hfactor : (clearedSkewPolyOf p).eval X Y =
      q.eval X Y * (X ^ 2 - 1) * (Y ^ 2 - 1))
    (hq : 0 ≤ q.eval X Y) :
    (reflectedVarianceSkewPolyOf p).eval X Y ≤ 0 := by
  have hXpos : 0 < X := _root_.lt_of_lt_of_le zero_lt_one hX
  have hYpos : 0 < Y := _root_.lt_of_lt_of_le zero_lt_one hY
  have hxf : 0 ≤ X ^ 2 - 1 := by
    calc
      0 ≤ (X - 1) * (X + 1) := mul_nonneg (sub_nonneg.mpr hX)
        (add_nonneg (zero_le_one.trans hX) zero_le_one)
      _ = X ^ 2 - 1 := by ring
  have hyf : 0 ≤ Y ^ 2 - 1 := by
    calc
      0 ≤ (Y - 1) * (Y + 1) := mul_nonneg (sub_nonneg.mpr hY)
        (add_nonneg (zero_le_one.trans hY) zero_le_one)
      _ = Y ^ 2 - 1 := by ring
  have hc : 0 ≤ (clearedSkewPolyOf p).eval X Y := by
    rw [hfactor]
    exact mul_nonneg (mul_nonneg hq hxf) hyf
  rw [eval_clearedSkewPolyOf_eq_scaled_neg_skew p X Y
    hXpos.ne' hYpos.ne'] at hc
  rw [mul_assoc] at hc
  have hscale : 0 < X ^ (-17 : Int) * Y ^ (17 : Int) :=
    mul_pos (zpow_pos hXpos _) (zpow_pos hYpos _)
  have hneg : 0 ≤ -(reflectedVarianceSkewPolyOf p).eval X Y :=
    (mul_nonneg_iff_of_pos_right hscale).mp hc
  linarith

end StatMech.FrontierA.NOneSymmetricMeanCertificate
