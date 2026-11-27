/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralTorusBands
public import MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints

/-!
# The native polynomial Chevalley quotient and its torus derivative

The Cartan space is Spec of the actual coordinate polynomial algebra.
Its quotient is Spec of the actual invariant subalgebra. The coordinate
action is bound to the linear action, which in turn is differentiated
from the actual torus action using every dual-number coefficient algebra.
Ramification is the actual reflection equalizer and actual root
hyperplane, rather than a set of closed points.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections0.5,1.4--1.7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CameralChevalleyModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open _root_.AlgebraicGeometry ExpansionParameterModels CameralTorusBands
open scoped BigOperators

variable {k : Type} [Field k] {r : ℕ}
  (T : TorusTheory k r) (Gm : TorusTheory k 1)
  (W : Type) [Group W] [Fintype W] (R : Roots T Gm W)

abbrev Cartan := Fin r → k
abbrev Coordinate := MvPolynomial (Fin r) k

def firstOrderPoint (A : CommAlgCat.{0} k) (v : Fin r → A) :
    TorusInfinitesimalPoints.doubled A ⟶ torusScheme k r :=
  (T.units (TorusInfinitesimalPoints.doubled A)).symm
    (fun i => Units.map (Scheme.ΓSpecIso (.of (TrivSqZeroExt A A))).inv.hom.toMonoidHom
      (TorusInfinitesimalPoints.unit A (v i)))

def extendLinear (e : Cartan (k := k) (r := r) ≃ₗ[k] Cartan (k := k) (r := r))
    (A : CommAlgCat.{0} k) (v : Fin r → A) : Fin r → A :=
  fun i => ∑ j, algebraMap k A (e (Pi.single j 1) i) * v j

structure Action where
  linear : W →* (Cartan (k := k) (r := r) ≃ₗ[k] Cartan (k := k) (r := r))
  polynomial : W →* (Coordinate (k := k) (r := r) ≃ₐ[k] Coordinate (k := k) (r := r))
  coordinate : ∀ (w : W) (i : Fin r),
    polynomial w (MvPolynomial.X i) =
      ∑ j, MvPolynomial.C (linear w⁻¹ (Pi.single j 1) i) * MvPolynomial.X j
  torus_derivative : ∀ (A : CommAlgCat.{0} k) (v : Fin r → A) (w : W),
    firstOrderPoint T A v ≫ (R.action w).asIso.hom =
      firstOrderPoint T A (extendLinear (linear w) A v)
  reflection : ∀ (i : Fin R.count) (v : Cartan (k := k) (r := r)) (j : Fin r),
    linear (R.reflection i) v j =
      v j - (∑ l, (R.exponent i l : k) * v l) * (R.coexponent i j : k)

variable (A : Action T Gm W R)

def invariants : Subalgebra k (Coordinate (k := k) (r := r)) where
  carrier := {f | ∀ w : W, A.polynomial w f = f}
  algebraMap_mem' c w := (A.polynomial w).commutes c
  zero_mem' w := map_zero _
  one_mem' w := map_one _
  add_mem' hf hg w := by rw [map_add, hf w, hg w]
  mul_mem' hf hg w := by rw [map_mul, hf w, hg w]

def space : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap k (Coordinate (k := k) (r := r)))

def quotient : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap k (invariants T Gm W R A))

def rootEquation (i : Fin R.count) : Coordinate (k := k) (r := r) :=
  ∑ j, MvPolynomial.C (R.exponent i j : k) * MvPolynomial.X j

def rootIdeal (i : Fin R.count) : Ideal (Coordinate (k := k) (r := r)) :=
  Ideal.span {rootEquation T Gm W R i}

structure Geometry where
  cover : WCover W (quotient T Gm W R A)
  total : cover.scheme.left ≅ (space (k := k) (r := r)).left
  projection : total.hom ≫ Spec.map (CommRingCat.ofHom
    (invariants T Gm W R A).val.toRingHom) = cover.scheme.hom
  action : ∀ w : W,
    (cover.action w).asIso.hom.left ≫ total.hom = total.hom ≫
      Spec.map (CommRingCat.ofHom (A.polynomial w⁻¹).toAlgHom.toRingHom)
  fixed : ∀ i : Fin R.count,
    equalizer (cover.action (R.reflection i)).asIso.hom.left (𝟙 cover.scheme.left) ≅
      Spec (.of ((Coordinate (k := k) (r := r)) ⧸ rootIdeal T Gm W R i))
  fixed_inclusion : ∀ i : Fin R.count,
    equalizer.ι (cover.action (R.reflection i)).asIso.hom.left (𝟙 cover.scheme.left) ≫
      total.hom = (fixed i).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (rootIdeal T Gm W R i)))

def Geometry.chevalley (H : Geometry T Gm W R A) : ChevalleyCover (k := k) W where
  base := quotient T Gm W R A
  cover := H.cover

end MathlibExt.AlgebraicGeometry.CameralChevalleyModels
