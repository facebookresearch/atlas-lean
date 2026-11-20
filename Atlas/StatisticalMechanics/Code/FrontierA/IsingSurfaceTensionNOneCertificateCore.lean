/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching
import Std.Data.TreeMap.Basic










open Finset
open Std

namespace StatMech.FrontierA
namespace NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

structure BiTerm where
  ex : Int
  ey : Int
  coeff : Int
  deriving DecidableEq, Repr

structure BiPoly where
  terms : List BiTerm
  deriving DecidableEq, Repr

def BiPoly.insert (t : BiTerm) : List BiTerm -> List BiTerm
  | [] => if t.coeff = 0 then [] else [t]
  | s :: ss =>
      if t.ex = s.ex && t.ey = s.ey then
        let c := s.coeff + t.coeff
        if c = 0 then ss else { s with coeff := c } :: ss
      else
        s :: insert t ss

def biExponentCompare (a b : Int × Int) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | o => o

abbrev BiTermMap := TreeMap (Int × Int) Int biExponentCompare

def BiPoly.ofTerms (ts : List BiTerm) : BiPoly :=
  let m : BiTermMap := ts.foldl (fun (out : BiTermMap) (t : BiTerm) =>
    out.alter (t.ex, t.ey) fun (o : Option Int) => match o with
      | none => if t.coeff = 0 then none else some (t.coeff : Int)
      | some (c : Int) =>
          if c + t.coeff = 0 then none else some (c + t.coeff))
    (TreeMap.empty : BiTermMap)
  ⟨m.toList.map fun t => { ex := t.1.1, ey := t.1.2, coeff := t.2 }⟩

def BiPoly.monomial (ex ey : Int) (coeff : Int) : BiPoly :=
  .ofTerms [{ ex := ex, ey := ey, coeff := coeff }]

def BiPoly.add (p q : BiPoly) : BiPoly :=
  .ofTerms (p.terms ++ q.terms)

def BiPoly.neg (p : BiPoly) : BiPoly :=
  .ofTerms (p.terms.map fun t => { t with coeff := -t.coeff })

def BiPoly.sub (p q : BiPoly) : BiPoly := p.add q.neg

def BiPoly.mul (p q : BiPoly) : BiPoly :=
  .ofTerms <| p.terms.flatMap fun s => q.terms.map fun t =>
    { ex := s.ex + t.ex, ey := s.ey + t.ey,
      coeff := s.coeff * t.coeff }

instance : Add BiPoly := ⟨BiPoly.add⟩
instance : Neg BiPoly := ⟨BiPoly.neg⟩
instance : Sub BiPoly := ⟨BiPoly.sub⟩
instance : Mul BiPoly := ⟨BiPoly.mul⟩

def BiPoly.sumCodes (f : Nat -> BiPoly) : BiPoly :=
  (List.range 512).foldl (fun p x => p.add (f x)) (.monomial 0 0 0)

def BiPoly.coeff (p : BiPoly) (ex ey : Int) : Int :=
  p.terms.foldl (fun c t =>
    if t.ex = ex && t.ey = ey then c + t.coeff else c) 0

def BiPoly.mapExponent (f : Int -> Int -> Int × Int) (p : BiPoly) : BiPoly :=
  .ofTerms <| p.terms.map fun t =>
    let e := f t.ex t.ey
    { ex := e.1, ey := e.2, coeff := t.coeff }

def BiPoly.scaleObservable (p : BiPoly) (power : Nat) : BiPoly :=
  .ofTerms <| p.terms.map fun t =>
    { t with coeff := t.coeff * (2 * t.ey - 9) ^ power }

def layerCodeBit (s : Nat) (p : Fin 3 × Fin 3) : Bool :=
  s.testBit (3 * p.1.val + p.2.val)

def spinInt (s : Nat) (p : Fin 3 × Fin 3) : Int :=
  if layerCodeBit s p then 1 else -1

def spinCode (s k : Nat) : Int := if s.testBit k then 1 else -1

def layerInternalInt (s : Nat) : Int :=
  spinCode s 0 * spinCode s 3 + spinCode s 1 * spinCode s 4 +
  spinCode s 2 * spinCode s 5 + spinCode s 3 * spinCode s 6 +
  spinCode s 4 * spinCode s 7 + spinCode s 5 * spinCode s 8 +
  spinCode s 0 * spinCode s 1 + spinCode s 1 * spinCode s 2 +
  spinCode s 3 * spinCode s 4 + spinCode s 4 * spinCode s 5 +
  spinCode s 6 * spinCode s 7 + spinCode s 7 * spinCode s 8

def layerBoundaryDegreeInt (p : Fin 3 × Fin 3) : Int :=
  (if p.1.val = 0 then 1 else 0) +
  (if p.1.val + 1 = 3 then 1 else 0) +
  (if p.2.val = 0 then 1 else 0) +
  (if p.2.val + 1 = 3 then 1 else 0)

def layerLateralInt (s : Nat) : Int :=
  layerInternalInt s +
    2 * spinCode s 0 + spinCode s 1 + 2 * spinCode s 2 +
    spinCode s 3 + spinCode s 5 +
    2 * spinCode s 6 + spinCode s 7 + 2 * spinCode s 8

def layerFaceInt (s : Nat) : Int :=
  spinCode s 0 + spinCode s 1 + spinCode s 2 +
    spinCode s 3 + spinCode s 4 + spinCode s 5 +
    spinCode s 6 + spinCode s 7 + spinCode s 8

def layerDotInt (s t : Nat) : Int :=
  spinCode s 0 * spinCode t 0 + spinCode s 1 * spinCode t 1 +
    spinCode s 2 * spinCode t 2 + spinCode s 3 * spinCode t 3 +
    spinCode s 4 * spinCode t 4 + spinCode s 5 * spinCode t 5 +
    spinCode s 6 * spinCode t 6 + spinCode s 7 * spinCode t 7 +
    spinCode s 8 * spinCode t 8

def halfShift (x shift : Int) : Int := (x + shift) / 2




def updateCoefficient : List Int -> Nat -> (Int -> Int) -> List Int
  | [], _, _ => []
  | x :: xs, 0, f => f x :: xs
  | x :: xs, i + 1, f => x :: updateCoefficient xs i f

def addCoefficientLists : List Int -> List Int -> List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addCoefficientLists xs ys


def rawMomentStatePoly (s : Nat) : BiPoly :=
  BiPoly.monomial (halfShift (layerLateralInt s) 16) 0 1 *
    (BiPoly.sumCodes fun v =>
      BiPoly.monomial
        (halfShift
          (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26)
        0 1) *
    (BiPoly.sumCodes fun q =>
      BiPoly.monomial
        (halfShift (layerLateralInt q + layerFaceInt q) 17)
        (halfShift (layerDotInt s q) 9) 1)


def rawMomentDirectBlock (start count : Nat) : BiPoly :=
  (List.range count).foldl
    (fun out offset => out.add (rawMomentStatePoly (start + offset)))
    (.monomial 0 0 0)



def rawMomentPolyStateSum : BiPoly :=
  (List.range 256).foldl
    (fun out block => out.add (rawMomentDirectBlock (2 * block) 2))
    (.monomial 0 0 0)




def rawMomentVCounts (s : Nat) : List Int :=
  (List.range 512).foldl (fun out v =>
    let ev := Int.toNat (halfShift
      (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26)
    updateCoefficient out ev (fun c => c + 1))
    (List.replicate 35 0)

def rawMomentQCounts (s : Nat) : List Int :=
  (List.range 512).foldl (fun out q =>
    let eq := Int.toNat
      (halfShift (layerLateralInt q + layerFaceInt q) 17)
    let iq := Int.toNat (halfShift (layerDotInt s q) 9)
    updateCoefficient out (10 * eq + iq) (fun c => c + 1))
    (List.replicate 260 0)

def addRawMomentState (out : List Int) (s : Nat) : List Int :=
  let se := Int.toNat (halfShift (layerLateralInt s) 16)
  let vCount := rawMomentVCounts s
  let qCount := rawMomentQCounts s
  (List.range 35).foldl (fun out ev =>
    (List.range 26).foldl (fun out eq =>
      (List.range 10).foldl (fun out iq =>
        let c := vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0
        let index := 10 * (se + ev + eq) + iq
        updateCoefficient out index (fun z => z + c)) out) out) out

def rawMomentStateCoefficientList (s : Nat) : List Int :=
  addRawMomentState (List.replicate 800 0) s



def rawMomentCoefficientSmallList (start count : Nat) : List Int :=
  (List.range count).foldl (fun out offset =>
    addCoefficientLists out (rawMomentStateCoefficientList (start + offset)))
    (List.replicate 800 0)



def rawMomentCoefficientBlockList (start : Nat) : Nat -> List Int
  | 0 => List.replicate 800 0
  | 1 => rawMomentCoefficientSmallList start 1
  | count + 2 =>
      addCoefficientLists (rawMomentCoefficientSmallList start 2)
        (rawMomentCoefficientBlockList (start + 2) count)

def rawMomentCoefficientBlock (start count : Nat) : Array Int :=
  (rawMomentCoefficientBlockList start count).toArray

def rawMomentCoefficientList : List Int :=
  (List.range 16).foldl (fun out block =>
    addCoefficientLists out (rawMomentCoefficientBlockList (32 * block) 32))
    (List.replicate 800 0)

def rawMomentCoefficientArray : Array Int :=
  rawMomentCoefficientList.toArray


def rawMomentPolyOfCoefficientList (coefficients : List Int) : BiPoly :=
  .ofTerms <| (List.range 80).flatMap fun (ex : Nat) =>
    (List.range 10).map fun (ey : Nat) =>
      { ex := (ex : Int), ey := (ey : Int),
        coeff := coefficients.getD (10 * ex + ey) 0 }




def rawMomentPoly : BiPoly :=
  rawMomentPolyOfCoefficientList rawMomentCoefficientList

def varianceNumeratorPolyOf (p : BiPoly) : BiPoly :=
  (p.scaleObservable 2 * p) -
    (p.scaleObservable 1 * p.scaleObservable 1)

def varianceNumeratorPoly : BiPoly := varianceNumeratorPolyOf rawMomentPoly

def reflectedVarianceSkewPolyOf (p : BiPoly) : BiPoly :=
  let n := varianceNumeratorPolyOf p
  let flipY := BiPoly.mapExponent (fun ex ey => (ex, -ey))
  n * (flipY p * flipY p) - flipY n * (p * p)

def reflectedVarianceSkewPoly : BiPoly :=
  reflectedVarianceSkewPolyOf rawMomentPoly



def clearedSkewPolyOf (p : BiPoly) : BiPoly :=
  ((reflectedVarianceSkewPolyOf p).neg).mapExponent
    (fun ex ey => (ex - 17, ey + 17))

def clearedSkewPoly : BiPoly := clearedSkewPolyOf rawMomentPoly

def BiPoly.xSquareSubOne : BiPoly :=
  .ofTerms [{ ex := 2, ey := 0, coeff := 1 },
    { ex := 0, ey := 0, coeff := -1 }]

def BiPoly.ySquareSubOne : BiPoly :=
  .ofTerms [{ ex := 0, ey := 2, coeff := 1 },
    { ex := 0, ey := 0, coeff := -1 }]

def BiPoly.leadingX (p : BiPoly) (e : Int) : BiPoly :=
  .ofTerms <| p.terms.filterMap fun t =>
    if t.ex = e then some t else none

def BiPoly.leadingY (p : BiPoly) (e : Int) : BiPoly :=
  .ofTerms <| p.terms.filterMap fun t =>
    if t.ey = e then some t else none

def BiPoly.divXsqSubOneStep (e : Int) (qr : BiPoly × BiPoly) :
    BiPoly × BiPoly :=
  let lead := qr.2.leadingX e
  let qadd := lead.mapExponent (fun ex ey => (ex - 2, ey))
  let correction := qadd.mul
    (.ofTerms [{ ex := 2, ey := 0, coeff := 1 },
      { ex := 0, ey := 0, coeff := -1 }])
  (qr.1.add qadd, qr.2.sub correction)

def BiPoly.divYsqSubOneStep (e : Int) (qr : BiPoly × BiPoly) :
    BiPoly × BiPoly :=
  let lead := qr.2.leadingY e
  let qadd := lead.mapExponent (fun ex ey => (ex, ey - 2))
  let correction := qadd.mul
    (.ofTerms [{ ex := 0, ey := 2, coeff := 1 },
      { ex := 0, ey := 0, coeff := -1 }])
  (qr.1.add qadd, qr.2.sub correction)

def descendingFrom (top : Nat) : List Int :=
  (List.range (top + 1)).reverse.map Int.ofNat

def BiPoly.divXsqSubOne (top : Nat) (p : BiPoly) : BiPoly × BiPoly :=
  (descendingFrom top).foldl (fun qr e => divXsqSubOneStep e qr)
    (.monomial 0 0 0, p)

def BiPoly.divYsqSubOne (top : Nat) (p : BiPoly) : BiPoly × BiPoly :=
  (descendingFrom top).foldl (fun qr e => divYsqSubOneStep e qr)
    (.monomial 0 0 0, p)


def quotientPolyOf (p : BiPoly) : BiPoly :=
  (((clearedSkewPolyOf p).divYsqSubOne 34).1.divXsqSubOne 294).1

def quotientPoly : BiPoly := quotientPolyOf rawMomentPoly

def quotientRemainderYOf (p : BiPoly) : BiPoly :=
  ((clearedSkewPolyOf p).divYsqSubOne 34).2

def quotientRemainderY : BiPoly := quotientRemainderYOf rawMomentPoly

def quotientRemainderXOf (p : BiPoly) : BiPoly :=
  (((clearedSkewPolyOf p).divYsqSubOne 34).1.divXsqSubOne 294).2

def quotientRemainderX : BiPoly := quotientRemainderXOf rawMomentPoly

def chooseInt (n k : Int) : Int :=
  if 0 <= n && 0 <= k then (Int.toNat n).choose (Int.toNat k) else 0


def BiPoly.shiftToOne (q : BiPoly) : BiPoly :=
  .ofTerms <| q.terms.flatMap fun t =>
    (List.range (Int.toNat t.ex + 1)).flatMap fun (a : Nat) =>
      (List.range (Int.toNat t.ey + 1)).map fun (b : Nat) =>
        { ex := (a : Int), ey := (b : Int),
          coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
            ((Int.toNat t.ey).choose b : Int) }


def shiftedQuotientPolyOf (p : BiPoly) : BiPoly :=
  (quotientPolyOf p).shiftToOne

def shiftedQuotientPoly : BiPoly := shiftedQuotientPolyOf rawMomentPoly

def remainderCertificateOf (p : BiPoly) : Bool :=
  (quotientRemainderYOf p).terms.isEmpty &&
    (quotientRemainderXOf p).terms.isEmpty

def remainderCertificate : Bool := remainderCertificateOf rawMomentPoly

def coefficientCertificateOf (p : BiPoly) : Bool :=
  (shiftedQuotientPolyOf p).terms.all fun t => decide (0 <= t.coeff)

def coefficientCertificate : Bool := coefficientCertificateOf rawMomentPoly

def certificateOf (p : BiPoly) : Bool :=
  remainderCertificateOf p && coefficientCertificateOf p

def certificate : Bool := certificateOf rawMomentPoly

end NOneSymmetricMeanCertificate
end StatMech.FrontierA
