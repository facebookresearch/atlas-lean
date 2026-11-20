/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusCycleHolonomy
import Code.FrontierA.KacWardAdaptiveClosure

open scoped Affine

namespace StatMech.FrontierA

def triangularIntStep : Fin 6 -> Int × Int :=
  ![(-1, 0), (1, 0), (0, -1), (0, 1), (-1, -1), (1, 1)]

def triangularIntPoint (p : Int × Int) : Complex :=
  (p.1 : Real) + (p.2 : Real) * Complex.I

def triangularCanonicalStep : Fin 3 -> Int × Int :=
  ![(1, 0), (0, 1), (1, 1)]

def triangularCanonicalKind : Fin 6 -> Fin 3 :=
  ![0, 0, 1, 1, 2, 2]

def triangularCanonicalBase (p : Int × Int) : Fin 6 -> Int × Int :=
  ![p + (-1, 0), p, p + (0, -1), p, p + (-1, -1), p]

theorem triangular_edge_eq_canonical (p : Int × Int) (a : Fin 6) :
    s(p, p + triangularIntStep a) =
      s(triangularCanonicalBase p a,
        triangularCanonicalBase p a +
          triangularCanonicalStep (triangularCanonicalKind a)) := by
  fin_cases a <;>
    simp [triangularIntStep, triangularCanonicalBase,
      triangularCanonicalStep, triangularCanonicalKind, Sym2.eq_iff,
      Prod.ext_iff] <;> omega

theorem triangular_sbtw_canonical_iff
    (p : Int × Int) (a : Fin 6) (z : Complex) :
    Sbtw Real (triangularIntPoint p) z
        (triangularIntPoint (p + triangularIntStep a)) ↔
      Sbtw Real (triangularIntPoint (triangularCanonicalBase p a)) z
        (triangularIntPoint (triangularCanonicalBase p a +
          triangularCanonicalStep (triangularCanonicalKind a))) := by
  fin_cases a <;>
    simp [triangularIntPoint, triangularIntStep, triangularCanonicalBase,
      triangularCanonicalStep, triangularCanonicalKind, sbtw_comm,
      Prod.ext_iff] <;> ring_nf

private theorem scratch_canonical_open_intersection_edge_eq
    (p q : Int × Int) (a b : Fin 3) (z : Complex)
    (hp : Sbtw Real (triangularIntPoint p) z
      (triangularIntPoint (p + triangularCanonicalStep a)))
    (hq : Sbtw Real (triangularIntPoint q) z
      (triangularIntPoint (q + triangularCanonicalStep b))) :
    s(p, p + triangularCanonicalStep a) =
      s(q, q + triangularCanonicalStep b) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  obtain ⟨t, ht, htz⟩ := hp.mem_image_Ioo
  obtain ⟨u, hu, huz⟩ := hq.mem_image_Ioo
  rcases ht with ⟨ht0, ht1⟩
  rcases hu with ⟨hu0, hu1⟩
  have heq : AffineMap.lineMap (triangularIntPoint (px, py))
        (triangularIntPoint ((px, py) + triangularCanonicalStep a)) t =
      AffineMap.lineMap (triangularIntPoint (qx, qy))
        (triangularIntPoint ((qx, qy) + triangularCanonicalStep b)) u :=
    htz.trans huz.symm
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  fin_cases a <;> fin_cases b <;>
    simp [triangularIntPoint, triangularCanonicalStep,
      AffineMap.lineMap_apply] at hre him ⊢
  all_goals
    try have hreCast : (px : Real) = (qx : Real) := by exact_mod_cast hre
    try have himCast : (py : Real) = (qy : Real) := by exact_mod_cast him
    have hxloR : (-2 : Real) < (qx : Real) - (px : Real) := by linarith
    have hxhiR : (qx : Real) - (px : Real) < 2 := by linarith
    have hyloR : (-2 : Real) < (qy : Real) - (py : Real) := by linarith
    have hyhiR : (qy : Real) - (py : Real) < 2 := by linarith
    have hxlo : (-2 : Int) < qx - px := by exact_mod_cast hxloR
    have hxhi : qx - px < (2 : Int) := by exact_mod_cast hxhiR
    have hylo : (-2 : Int) < qy - py := by exact_mod_cast hyloR
    have hyhi : qy - py < (2 : Int) := by exact_mod_cast hyhiR
    interval_cases hx : qx - px <;>
      interval_cases hy : qy - py <;>
      have hxR := congrArg (fun x : Int => (x : Real)) hx <;>
      have hyR := congrArg (fun x : Int => (x : Real)) hy <;>
      push_cast at hxR hyR <;>
      norm_num at hxR hyR <;>
      first
      | (exfalso; linarith)
      | omega

theorem scratch_open_intersection_edge_eq
    (p q : Int × Int) (a b : Fin 6) (z : Complex)
    (hp : Sbtw Real (triangularIntPoint p) z
      (triangularIntPoint (p + triangularIntStep a)))
    (hq : Sbtw Real (triangularIntPoint q) z
      (triangularIntPoint (q + triangularIntStep b))) :
    s(p, p + triangularIntStep a) =
      s(q, q + triangularIntStep b) := by
  rw [triangular_edge_eq_canonical p a,
    triangular_edge_eq_canonical q b]
  exact scratch_canonical_open_intersection_edge_eq
    (triangularCanonicalBase p a) (triangularCanonicalBase q b)
    (triangularCanonicalKind a) (triangularCanonicalKind b) z
    ((triangular_sbtw_canonical_iff p a z).mp hp)
    ((triangular_sbtw_canonical_iff q b z).mp hq)

end StatMech.FrontierA
