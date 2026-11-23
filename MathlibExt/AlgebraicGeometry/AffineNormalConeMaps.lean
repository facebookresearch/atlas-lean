/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineConeAtlas

/-!
# Coefficient- and degree-one-normalized maps of actual Rees normal algebras

The model is B tensor_A Rees(ker(A→B)), with the actual commutative square
of coefficient rings. Every map is fixed on B and every degree-one ideal
element. These generate the whole normal algebra by Mathlib's
adjoin_monomial_eq_reesAlgebra, so no unspecified cone morphism is hidden.

The ordinary producer is a source integration dependency: Mathlib
RingTheory/ReesAlgebra.lean (Andrew Yang, 2022), revision
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0. Global normal-cone
constructions are source integration in AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b. This module supplies their
affine map contract; it does not claim to supply that producer. Identity
and composition use the actual ring homomorphisms below.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineNormalConeMaps

open AffineConeAtlas

variable {k l m B C D : Type} [CommRing k] [CommRing l] [CommRing m]
  [CommRing B] [CommRing C] [CommRing D] [Algebra k B] [Algebra l C] [Algebra m D]
  (P : Algebra.Extension.{0} k B) (Q : Algebra.Extension.{0} l C)
  (S : Algebra.Extension.{0} m D)

def kernelImage (phi : P.Ring →+* Q.Ring) (beta : B →+* C)
    (h : (algebraMap Q.Ring C).comp phi = beta.comp (algebraMap P.Ring B))
    (x : P.ker) : Q.ker :=
  ⟨phi x.val, by
    change algebraMap Q.Ring C (phi x.val) = 0
    have he := RingHom.congr_fun h x.val
    change algebraMap Q.Ring C (phi x.val) = beta (algebraMap P.Ring B x.val) at he
    rw [he]
    have hx : algebraMap P.Ring B x.val = 0 := x.property
    rw [hx, map_zero]⟩

structure NormalMap (phi : P.Ring →+* Q.Ring) (beta : B →+* C)
    (h : (algebraMap Q.Ring C).comp phi = beta.comp (algebraMap P.Ring B)) where
  map : normalAlgebra P →+* normalAlgebra Q
  coefficient : ∀ b : B,
    map (algebraMap B (normalAlgebra P) b) = algebraMap C (normalAlgebra Q) (beta b)
  degreeOne : ∀ x : P.ker,
    map (normalDegreeOne P x) = normalDegreeOne Q (kernelImage P Q phi beta h x)

def identity : NormalMap P P (RingHom.id _) (RingHom.id _) (by rfl) where
  map := RingHom.id _
  coefficient _ := rfl
  degreeOne _ := rfl

theorem composedSquare (phi : P.Ring →+* Q.Ring) (beta : B →+* C)
    (h : (algebraMap Q.Ring C).comp phi = beta.comp (algebraMap P.Ring B))
    (psi : Q.Ring →+* S.Ring) (gamma : C →+* D)
    (j : (algebraMap S.Ring D).comp psi = gamma.comp (algebraMap Q.Ring C)) :
    (algebraMap S.Ring D).comp (psi.comp phi) =
      (gamma.comp beta).comp (algebraMap P.Ring B) := by
  ext x
  exact (RingHom.congr_fun j (phi x)).trans (congrArg gamma (RingHom.congr_fun h x))

def compose {phi : P.Ring →+* Q.Ring} {beta : B →+* C}
    {h : (algebraMap Q.Ring C).comp phi = beta.comp (algebraMap P.Ring B)}
    {psi : Q.Ring →+* S.Ring} {gamma : C →+* D}
    {j : (algebraMap S.Ring D).comp psi = gamma.comp (algebraMap Q.Ring C)}
    (F : NormalMap P Q phi beta h) (G : NormalMap Q S psi gamma j) :
    NormalMap P S (psi.comp phi) (gamma.comp beta)
      (composedSquare P Q S phi beta h psi gamma j) where
  map := G.map.comp F.map
  coefficient b := by
    change G.map (F.map _) = _
    rw [F.coefficient, G.coefficient]
    rfl
  degreeOne x := by
    change G.map (F.map _) = _
    rw [F.degreeOne, G.degreeOne]
    rfl

end MathlibExt.AlgebraicGeometry.AffineNormalConeMaps
