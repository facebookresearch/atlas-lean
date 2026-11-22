/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LeftHornFaces

/-!
# The cancellation horn of an actual triangle

A triangle `e; h = e` and the two right-unit triangles determine an original
left outer three-horn. Every filler of that horn exhibits `h` as the identity
in the homotopy category. The construction does not choose or alter a base map.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CocartesianEdge

/-- The three prescribed faces used to cancel an actual triangle before an edge. -/
def cancellationFaces {X : SSet.{u}} {x y : X _⦋0⦌} {e : Edge x y} {h : Edge y y}
    (H : Edge.CompStruct e h e) (j : Fin 4) (_ : j ≠ (0 : Fin 4)) :
    (Δ[2] : SSet.{u}) ⟶ X :=
  if j = 3 then yonedaEquiv.symm H.simplex
  else yonedaEquiv.symm (Edge.CompStruct.compId e).simplex

/-- The original triangle and right-unit triangles agree on every common edge. -/
theorem cancellationFaces_compatible {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : Edge x y} {h : Edge y y} (H : Edge.CompStruct e h e) :
    horn.IsCompatible (cancellationFaces H) := by
  let U := Edge.CompStruct.compId e
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
  have hkv : k.val ≠ 0 := fun h => hk (Fin.ext h)
  have hjkv : j.val < k.val := hjk
  fin_cases j <;> fin_cases k <;> try omega
  all_goals simp_all [cancellationFaces, stdSimplex.δ_comp_yonedaEquiv_symm,
    H.d₁, ← show U = Edge.CompStruct.compId e from rfl, U.d₂, U.d₁]
  change e.edge = X.δ (2 : Fin 3) H.simplex
  exact H.d₂.symm

/-- The literal left three-horn glued from the triangle and two right units. -/
def cancellationHorn {X : SSet.{u}} {x y : X _⦋0⦌} {e : Edge x y} {h : Edge y y}
    (H : Edge.CompStruct e h e) : (Λ[3, (0 : Fin 4)] : SSet.{u}) ⟶ X :=
  (cancellationFaces_compatible H).desc

/-- Each included face is the originally specified triangle or right unit. -/
theorem cancellationHorn_face {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : Edge x y} {h : Edge y y} (H : Edge.CompStruct e h e)
    (j : Fin 4) (hj : j ≠ (0 : Fin 4)) :
    horn.ι ((0 : Fin 4)) j hj ≫ cancellationHorn H = cancellationFaces H j hj :=
  (cancellationFaces_compatible H).ι_desc j hj

/-- The critical first edge is the whole original edge being cancelled against. -/
theorem cancellationHorn_edge {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : Edge x y} {h : Edge y y} (H : Edge.CompStruct e h e) :
    (leftHornEdge (cancellationHorn H)).edge = e.edge := by
  rw [leftHornEdge_three, cancellationHorn_face]
  simp only [cancellationFaces, ite_true, Equiv.apply_symm_apply, H.d₂]

/-- A filler of this specified horn makes the original endomorphism the identity in Ho. -/
theorem toHoHom_eq_id_of_cancellationHorn_fill {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : Edge x y} {h : Edge y y} (H : Edge.CompStruct e h e)
    (T : (Δ[3] : SSet.{u}) ⟶ X)
    (hT : Λ[3, (0 : Fin 4)].ι ≫ T = cancellationHorn H) :
    h.toHoHom = 𝟙 (HomotopyCategory.mk y : hoFunctor.obj X) := by
  let U := Edge.CompStruct.compId e
  have face (j : Fin 4) (hj : j ≠ 0) :
      stdSimplex.δ j ≫ T = cancellationFaces H j hj := by
    rw [← horn.ι_ι_assoc (0 : Fin 4) j hj, hT, cancellationHorn_face]
  have d₁ : X.δ (1 : Fin 4) (yonedaEquiv T) = U.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, face 1 (by decide)]
    simp only [cancellationFaces, show (1 : Fin 4) ≠ 3 by decide, ite_false,
      Equiv.apply_symm_apply, U]
  have d₂ : X.δ (2 : Fin 4) (yonedaEquiv T) = U.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, face 2 (by decide)]
    simp only [cancellationFaces, show (2 : Fin 4) ≠ 3 by decide, ite_false,
      Equiv.apply_symm_apply, U]
  have d₃ : X.δ (3 : Fin 4) (yonedaEquiv T) = H.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, face 3 (by decide)]
    simp only [cancellationFaces, ite_true, Equiv.apply_symm_apply]
  have face₀ : X.δ (0 : Fin 3) (X.δ (0 : Fin 4) (yonedaEquiv T)) = (Edge.id y).edge := by
    have hi := δ_comp_δ_self_apply (S := X) (i := (0 : Fin 3)) (yonedaEquiv T)
    change X.δ 0 (X.δ 0 (yonedaEquiv T)) = X.δ 0 (X.δ 1 (yonedaEquiv T)) at hi
    rw [hi, d₁, U.d₀]
  have face₁ : X.δ (1 : Fin 3) (X.δ (0 : Fin 4) (yonedaEquiv T)) = (Edge.id y).edge := by
    have hi := δ_comp_δ''_apply (S := X) (i := (0 : Fin 4)) (j := (1 : Fin 3))
      (by decide) (yonedaEquiv T)
    change X.δ 0 (X.δ 2 (yonedaEquiv T)) = X.δ 1 (X.δ 0 (yonedaEquiv T)) at hi
    rw [← hi, d₂, U.d₀]
  have face₂ : X.δ (2 : Fin 3) (X.δ (0 : Fin 4) (yonedaEquiv T)) = h.edge := by
    have hi := δ_comp_δ''_apply (S := X) (i := (0 : Fin 4)) (j := (2 : Fin 3))
      (by decide) (yonedaEquiv T)
    change X.δ 0 (X.δ 3 (yonedaEquiv T)) = X.δ 2 (X.δ 0 (yonedaEquiv T)) at hi
    rw [← hi, d₃, H.d₀]
  let K : Edge.CompStruct h (Edge.id y) (Edge.id y) :=
    Edge.CompStruct.mk (X.δ (0 : Fin 4) (yonedaEquiv T)) face₂ face₀ face₁
  have hh := Edge.toHoHom_comp K
  simpa only [Edge.toHoHom_id, Category.comp_id] using hh

end SSet.CocartesianEdge
