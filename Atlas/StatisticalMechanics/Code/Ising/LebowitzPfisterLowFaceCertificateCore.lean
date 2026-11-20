/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Data.List.FinRange
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic



open Finset

namespace StatMech.Ising
namespace LowFaceCertificate

structure TriTerm where
  ex : Nat
  ey : Nat
  ez : Nat
  coeff : Int
  deriving DecidableEq

structure TriPoly where
  terms : List TriTerm

def TriPoly.insert (t : TriTerm) : List TriTerm -> List TriTerm
  | [] => [t]
  | s :: ss =>
      if t.ex = s.ex ∧ t.ey = s.ey ∧ t.ez = s.ez then
        { s with coeff := s.coeff + t.coeff } :: ss
      else
        s :: insert t ss

def TriPoly.ofTerms (ts : List TriTerm) : TriPoly :=
  ⟨ts.foldl (fun out t => insert t out) []⟩

def TriPoly.const (q : Int) : TriPoly :=
  ⟨[{ ex := 0, ey := 0, ez := 0, coeff := q }]⟩

def TriPoly.add (p q : TriPoly) : TriPoly := .ofTerms (p.terms ++ q.terms)

def TriPoly.neg (p : TriPoly) : TriPoly :=
  ⟨p.terms.map fun t => { t with coeff := -t.coeff }⟩

def TriPoly.mul (p q : TriPoly) : TriPoly :=
  .ofTerms <| p.terms.flatMap fun s => q.terms.map fun t =>
    { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez,
      coeff := s.coeff * t.coeff }

def TriPoly.pow (p : TriPoly) : Nat -> TriPoly
  | 0 => .const 1
  | n + 1 => p.mul (p.pow n)

instance : OfNat TriPoly n where ofNat := .const n
instance : Add TriPoly := ⟨TriPoly.add⟩
instance : Neg TriPoly := ⟨TriPoly.neg⟩
instance : Sub TriPoly := ⟨fun p q => p.add q.neg⟩
instance : Mul TriPoly := ⟨TriPoly.mul⟩
instance : Pow TriPoly Nat := ⟨TriPoly.pow⟩

def vx : TriPoly := ⟨[{ ex := 1, ey := 0, ez := 0, coeff := 1 }]⟩
def vy : TriPoly := ⟨[{ ex := 0, ey := 1, ez := 0, coeff := 1 }]⟩
def vz : TriPoly := ⟨[{ ex := 0, ey := 0, ez := 1, coeff := 1 }]⟩

def crossCoeffPoly (i j k : Nat) : TriPoly :=
  let x := vx
  let y := vy
  let z := vz
  let m1 (u : Nat) : Int := 252 * u
  let m11 (u v : Nat) : Int := 36 * u * v
  let m21 (u v : Nat) : Int := 6 * u * (u - 1) * v
  1764 * y * z * (x - x ^ 3 + y - y ^ 3 + z - z ^ 3) +
    .const (m1 i) * (9 * x * y * z * (x + y) * (1 - y)) +
    .const (m1 j) * (9 * x * y * z * (x + z) * (1 - z)) +
    .const (m1 k) * (9 * y ^ 2 * z * (y + z) * (1 - z)) -
    .const (m11 i j) *
      (3 * x * y * z * (3 - 2 * x) * (1 - y) * (1 - z)) +
    .const (m21 i j) * (6 * x ^ 2 * z * (1 - y) ^ 2 * (1 - z)) +
    .const (m21 j i) * (6 * x ^ 2 * y * (1 - y) * (1 - z) ^ 2) -
    .const (m11 i k) *
      (3 * x * y * z * (3 - 2 * y) * (1 - y) * (1 - z)) +
    .const (m21 i k) * (6 * x * y * z * (1 - y) ^ 2 * (1 - z)) +
    .const (m21 k i) * (6 * x * y ^ 2 * (1 - y) * (1 - z) ^ 2) -
    .const (m11 j k) *
      (3 * x * y ^ 2 * (3 - 2 * z) * (1 - z) ^ 2) +
    .const (m21 j k) * (6 * x * y ^ 2 * (1 - z) ^ 3) +
    .const (m21 k j) * (6 * x * y ^ 2 * (1 - z) ^ 3)

def radialize (p : TriPoly) : TriPoly :=
  let r := vx
  let q := vy
  let h := vz
  let d := 1 + q + r * q
  .ofTerms <| p.terms.flatMap fun t =>
    let degree := t.ex + t.ey + t.ez
    (.const t.coeff * r ^ t.ex * q ^ (t.ex + t.ey) *
      h ^ (degree - 3) * d ^ (6 - degree)).terms

def scaledBernFactor (n scale e i : Nat) : Int :=
  (i.choose e : Int) * (scale / (n.choose e : Int))

def radialBernCoeffOf (p : TriPoly)
    (a : Fin 13) (b : Fin 8) (c : Fin 4) : Int :=
  p.terms.foldl (fun q t => q + t.coeff *
    scaledBernFactor 12 27720 t.ex a *
    scaledBernFactor 7 105 t.ey b *
    scaledBernFactor 3 3 t.ez c) 0

def radialBernCoeff (i j k : Fin 8)
    (a : Fin 13) (b : Fin 8) (c : Fin 4) : Int :=
  radialBernCoeffOf (radialize (crossCoeffPoly i j k)) a b c

def radialCertificateFor (p : TriPoly) : Bool :=
  (List.finRange 13).all fun a =>
    (List.finRange 8).all fun b =>
      (List.finRange 4).all fun c => decide (0 <= radialBernCoeffOf p a b c)

def radialCertificateAtIJ (i j : Fin 8) : Bool :=
  (List.finRange 8).all fun k =>
    radialCertificateFor (radialize (crossCoeffPoly i j k))

def radialCertificateAt (i : Fin 8) : Bool :=
  (List.finRange 8).all fun j => radialCertificateAtIJ i j

end LowFaceCertificate
end StatMech.Ising
