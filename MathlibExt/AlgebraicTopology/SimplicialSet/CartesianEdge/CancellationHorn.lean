/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornFaces

/-!
# The cancellation horn of an actual triangle

A triangle `h; e = e` and the two left-unit triangles determine an original
right outer three-horn. Every filler of that horn exhibits `h` as the identity
in the homotopy category. The construction does not choose or alter a base map.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- The three prescribed faces used to cancel an actual triangle before an edge. -/
def cancellationFaces {X : SSet.{u}} {x y : X _⦋0⦌} {e : Edge x y} {h : Edge x x}
    (H : Edge.CompStruct h e e) (j : Fin 4) (_ : j ≠ Fin.last 3) :
    (Δ[2] : SSet.{u}) ⟶ X :=
  if j = 0 then yonedaEquiv.symm H.simplex
  else yonedaEquiv.symm (Edge.CompStruct.idComp e).simplex

/-- The original triangle and left-unit triangles agree on every common edge. -/
theorem cancellationFaces_compatible {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : Edge x y} {h : Edge x x} (H : Edge.CompStruct h e e) :
    horn.IsCompatible (cancellationFaces H) := by
  let U := Edge.CompStruct.idComp e
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hjv : j.val ≠ 3 := fun h => hj (Fin.ext h)
  have hkv : k.val ≠ 3 := fun h => hk (Fin.ext h)
  have hjkv : j.val < k.val := hjk
  fin_cases j <;> fin_cases k <;> try omega
  all_goals simp_all [cancellationFaces, stdSimplex.δ_comp_yonedaEquiv_symm,
    H.d₀, H.d₁, ← show U = Edge.CompStruct.idComp e from rfl, U.d₀, U.d₁]

/-- The literal right three-horn glued from the triangle and two left units. -/
def cancellationHorn {X : SSet.{u}} {x y : X _⦋0⦌} {e : Edge x y} {h : Edge x x}
    (H : Edge.CompStruct h e e) : (Λ[3, Fin.last 3] : SSet.{u}) ⟶ X :=
  (cancellationFaces_compatible H).desc

/-- Each included face is the originally specified triangle or left unit. -/
theorem cancellationHorn_face {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : Edge x y} {h : Edge x x} (H : Edge.CompStruct h e e)
    (j : Fin 4) (hj : j ≠ Fin.last 3) :
    horn.ι (Fin.last 3) j hj ≫ cancellationHorn H = cancellationFaces H j hj :=
  (cancellationFaces_compatible H).ι_desc j hj

/-- The critical last edge is the whole original edge being cancelled against. -/
theorem cancellationHorn_edge {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : Edge x y} {h : Edge x x} (H : Edge.CompStruct h e e) :
    (rightHornEdge (cancellationHorn H)).edge = e.edge := by
  rw [rightHornEdge_three, cancellationHorn_face]
  simp only [cancellationFaces, ite_true, Equiv.apply_symm_apply, H.d₀]

/-- A filler of this specified horn makes the original endomorphism the identity in Ho. -/
theorem toHoHom_eq_id_of_cancellationHorn_fill {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : Edge x y} {h : Edge x x} (H : Edge.CompStruct h e e)
    (T : (Δ[3] : SSet.{u}) ⟶ X)
    (hT : Λ[3, Fin.last 3].ι ≫ T = cancellationHorn H) :
    h.toHoHom = 𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) := by
  let U := Edge.CompStruct.idComp e
  have hT₀ : stdSimplex.δ (0 : Fin 4) ≫ T = yonedaEquiv.symm H.simplex := by
    rw [← horn.ι_ι_assoc (Fin.last 3) (0 : Fin 4) (by decide), hT,
      cancellationHorn_face]
    simp only [cancellationFaces, ite_true]
  have hT₁ : stdSimplex.δ (1 : Fin 4) ≫ T = yonedaEquiv.symm U.simplex := by
    rw [← horn.ι_ι_assoc (Fin.last 3) (1 : Fin 4) (by decide), hT,
      cancellationHorn_face]
    simp only [cancellationFaces, show (1 : Fin 4) ≠ 0 by decide, ite_false, U]
  have hT₂ : stdSimplex.δ (2 : Fin 4) ≫ T = yonedaEquiv.symm U.simplex := by
    rw [← horn.ι_ι_assoc (Fin.last 3) (2 : Fin 4) (by decide), hT,
      cancellationHorn_face]
    simp only [cancellationFaces, show (2 : Fin 4) ≠ 0 by decide, ite_false, U]
  have d₀ : X.δ (0 : Fin 4) (yonedaEquiv T) = H.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hT₀, Equiv.apply_symm_apply]
  have d₁ : X.δ (1 : Fin 4) (yonedaEquiv T) = U.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hT₁, Equiv.apply_symm_apply]
  have d₂ : X.δ (2 : Fin 4) (yonedaEquiv T) = U.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hT₂, Equiv.apply_symm_apply]
  have face₀ : X.δ (0 : Fin 3) (X.δ (3 : Fin 4) (yonedaEquiv T)) = h.edge := by
    have hi := δ_comp_δ'_apply (S := X) (i := (0 : Fin 3)) (j := (3 : Fin 4))
      (by decide) (yonedaEquiv T)
    change X.δ 0 (X.δ 3 (yonedaEquiv T)) = X.δ 2 (X.δ 0 (yonedaEquiv T)) at hi
    rw [hi, d₀, H.d₂]
  have face₁ : X.δ (1 : Fin 3) (X.δ (3 : Fin 4) (yonedaEquiv T)) = (Edge.id x).edge := by
    have hi := δ_comp_δ'_apply (S := X) (i := (1 : Fin 3)) (j := (3 : Fin 4))
      (by decide) (yonedaEquiv T)
    change X.δ 1 (X.δ 3 (yonedaEquiv T)) = X.δ 2 (X.δ 1 (yonedaEquiv T)) at hi
    rw [hi, d₁, U.d₂]
  have face₂ : X.δ (2 : Fin 3) (X.δ (3 : Fin 4) (yonedaEquiv T)) = (Edge.id x).edge := by
    have hi := δ_comp_δ'_apply (S := X) (i := (2 : Fin 3)) (j := (3 : Fin 4))
      (by decide) (yonedaEquiv T)
    change X.δ 2 (X.δ 3 (yonedaEquiv T)) = X.δ 2 (X.δ 2 (yonedaEquiv T)) at hi
    rw [hi, d₂, U.d₂]
  let K : Edge.CompStruct (Edge.id x) h (Edge.id x) :=
    Edge.CompStruct.mk (X.δ (3 : Fin 4) (yonedaEquiv T)) face₂ face₀ face₁
  have hh := Edge.toHoHom_comp K
  simpa only [Edge.toHoHom_id, Category.id_comp] using hh

end SSet.CartesianEdge
