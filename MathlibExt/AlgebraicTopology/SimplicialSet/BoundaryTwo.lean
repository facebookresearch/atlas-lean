/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Two-simplex boundary gluing

The boundary `∂Δ[2]` is the union of its three edges.
Mathematically it is obtained by a two-step pushout gluing:

* first glue the edges `0–1` (`face {0,1} = face {2}ᶜ`) and `0–2`
  (`face {0,2} = face {1}ᶜ`) along the vertex `0` (`face {0}`),
  obtaining the horn `Λ[2,0] = face {0,1} ⊔ face {0,2}`;
* then glue this horn with the remaining edge `1–2`
  (`face {1,2} = face {0}ᶜ`) along the two vertices `1,2`
  (`face {1} ⊔ face {2}`), obtaining `∂Δ[2]`.

Both steps are `SSet.Subcomplex.BicartSq.isPushout` pushouts in the
lattice of subcomplexes of `Δ[2]`.  This is the standard
two-step description of the boundary of a 2-simplex (cf.
Goerss–Jardine, *Simplicial Homotopy Theory*, Ch. I, §1;
Hovey, *Model Categories*).

The resulting map `SSet.boundary.twoDesc` takes three compatible
1-simplices `e01 : Δ[1] → X` (edge `0–1`), `e02 : Δ[1] → X`
(edge `0–2`), `e12 : Δ[1] → X` (edge `1–2`) with the three
vertex compatibilities and glues them to a map `∂Δ[2] → X`
with the correct face restrictions `face 0 = e12`, `face 1 = e02`,
`face 2 = e01`.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial SSet

namespace SSet
namespace boundary

variable {X : SSet.{u}}

/- Implementation helpers for `∂Δ[2]` gluing.
These are public only to satisfy Lean's module visibility for `twoDesc`
and its restriction lemmas; the intended public API is `twoDesc`,
`twoDesc_ι_zero/one/two`, and `hom_ext_two`. -/
namespace Impl

-- Subcomplexes of `Δ[2]` used in the two-step gluing.
abbrev F₀ : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face ({0}ᶜ : Finset (Fin 3))
abbrev F₁ : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face ({1}ᶜ : Finset (Fin 3))
abbrev F₂ : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face ({2}ᶜ : Finset (Fin 3))
abbrev V₀ : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face ({0} : Finset (Fin 3))
abbrev V₁ : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face ({1} : Finset (Fin 3))
abbrev V₂ : (Δ[2] : SSet.{u}).Subcomplex := stdSimplex.face ({2} : Finset (Fin 3))
abbrev I₁₂ : (Δ[2] : SSet.{u}).Subcomplex := F₂ ⊔ F₁
abbrev V₁₂ : (Δ[2] : SSet.{u}).Subcomplex := V₁ ⊔ V₂
abbrev B₂ : (Δ[2] : SSet.{u}).Subcomplex := SSet.boundary 2

-- Isomorphisms to the standard simplices.
noncomputable def isoF₀ : Δ[1] ≅ (F₀ : SSet.{u}) :=
  stdSimplex.faceSingletonComplIso (0 : Fin 3)
noncomputable def isoF₁ : Δ[1] ≅ (F₁ : SSet.{u}) :=
  stdSimplex.faceSingletonComplIso (1 : Fin 3)
noncomputable def isoF₂ : Δ[1] ≅ (F₂ : SSet.{u}) :=
  stdSimplex.faceSingletonComplIso (2 : Fin 3)
noncomputable def isoV₀ : Δ[0] ≅ (V₀ : SSet.{u}) :=
  stdSimplex.faceSingletonIso (0 : Fin 3)
noncomputable def isoV₁ : Δ[0] ≅ (V₁ : SSet.{u}) :=
  stdSimplex.faceSingletonIso (1 : Fin 3)
noncomputable def isoV₂ : Δ[0] ≅ (V₂ : SSet.{u}) :=
  stdSimplex.faceSingletonIso (2 : Fin 3)

lemma V₀_le_F₂ : V₀ ≤ F₂ := by
  rw [V₀, F₂, stdSimplex.face_le_face_iff]
  decide
lemma V₀_le_F₁ : V₀ ≤ F₁ := by
  rw [V₀, F₁, stdSimplex.face_le_face_iff]
  decide
lemma V₁_le_F₀ : V₁ ≤ F₀ := by
  rw [V₁, F₀, stdSimplex.face_le_face_iff]
  decide
lemma V₂_le_F₀ : V₂ ≤ F₀ := by
  rw [V₂, F₀, stdSimplex.face_le_face_iff]
  decide
lemma V₁_le_F₂ : V₁ ≤ F₂ := by
  rw [V₁, F₂, stdSimplex.face_le_face_iff]
  decide
lemma V₂_le_F₁ : V₂ ≤ F₁ := by
  rw [V₂, F₁, stdSimplex.face_le_face_iff]
  decide
lemma F₂_le_I₁₂ : F₂ ≤ I₁₂ := le_sup_left
lemma F₁_le_I₁₂ : F₁ ≤ I₁₂ := le_sup_right
lemma V₁_le_V₁₂ : V₁ ≤ V₁₂ := le_sup_left
lemma V₂_le_V₁₂ : V₂ ≤ V₁₂ := le_sup_right
lemma V₁₂_le_F₀ : V₁₂ ≤ F₀ :=
  sup_le V₁_le_F₀ V₂_le_F₀
lemma V₁₂_le_I₁₂ : V₁₂ ≤ I₁₂ :=
  sup_le (le_trans V₁_le_F₂ F₂_le_I₁₂) (le_trans V₂_le_F₁ F₁_le_I₁₂)
lemma F₀_le_B₂ : F₀ ≤ B₂ :=
  SSet.face_singleton_compl_le_boundary 0
lemma F₁_le_B₂ : F₁ ≤ B₂ :=
  SSet.face_singleton_compl_le_boundary 1
lemma F₂_le_B₂ : F₂ ≤ B₂ :=
  SSet.face_singleton_compl_le_boundary 2
lemma I₁₂_le_B₂ : I₁₂ ≤ B₂ :=
  sup_le F₂_le_B₂ F₁_le_B₂

lemma F₂_inf_F₁_eq_V₀ : F₂ ⊓ F₁ = V₀ := by
  change stdSimplex.face ({2}ᶜ : Finset (Fin 3)) ⊓ stdSimplex.face ({1}ᶜ : Finset (Fin 3)) =
    stdSimplex.face ({0} : Finset (Fin 3))
  rw [stdSimplex.face_inter_face]
  have h : (({2}ᶜ : Finset (Fin 3)) ⊓ {1}ᶜ) = ({0} : Finset (Fin 3)) := by decide
  rw [h]

lemma F₀_inf_F₂_eq_V₁ : F₀ ⊓ F₂ = V₁ := by
  change stdSimplex.face ({0}ᶜ : Finset (Fin 3)) ⊓ stdSimplex.face ({2}ᶜ : Finset (Fin 3)) =
    stdSimplex.face ({1} : Finset (Fin 3))
  rw [stdSimplex.face_inter_face]
  have h : (({0}ᶜ : Finset (Fin 3)) ⊓ {2}ᶜ) = ({1} : Finset (Fin 3)) := by decide
  rw [h]

lemma F₀_inf_F₁_eq_V₂ : F₀ ⊓ F₁ = V₂ := by
  change stdSimplex.face ({0}ᶜ : Finset (Fin 3)) ⊓ stdSimplex.face ({1}ᶜ : Finset (Fin 3)) =
    stdSimplex.face ({2} : Finset (Fin 3))
  rw [stdSimplex.face_inter_face]
  have h : (({0}ᶜ : Finset (Fin 3)) ⊓ {1}ᶜ) = ({2} : Finset (Fin 3)) := by decide
  rw [h]

lemma V₁_inf_V₂_eq_bot : V₁ ⊓ V₂ = (⊥ : (Δ[2] : SSet.{u}).Subcomplex) := by
  change stdSimplex.face ({1} : Finset (Fin 3)) ⊓ stdSimplex.face ({2} : Finset (Fin 3)) = ⊥
  rw [stdSimplex.face_inter_face]
  have h : (({1} : Finset (Fin 3)) ⊓ {2} : Finset (Fin 3)) = ∅ := by decide
  rw [h, stdSimplex.face_empty]

lemma B₂_eq_sup : B₂ = F₀ ⊔ F₁ ⊔ F₂ := by
  change SSet.boundary 2 = _
  rw [SSet.boundary_eq_iSup (n := 2)]
  have h : (⨆ i : Fin 3, stdSimplex.face ({i}ᶜ : Finset (Fin 3))) =
      stdSimplex.face ({0}ᶜ : Finset (Fin 3)) ⊔
      stdSimplex.face ({1}ᶜ : Finset (Fin 3)) ⊔
      stdSimplex.face ({2}ᶜ : Finset (Fin 3)) := by
    apply le_antisymm
    · apply iSup_le
      intro i
      fin_cases i
      · exact le_trans le_sup_left le_sup_left
      · exact le_trans le_sup_right le_sup_left
      · exact le_sup_right
    · apply sup_le
      · apply sup_le
        · exact le_iSup (fun i : Fin 3 => stdSimplex.face ({i}ᶜ : Finset (Fin 3))) 0
        · exact le_iSup (fun i : Fin 3 => stdSimplex.face ({i}ᶜ : Finset (Fin 3))) 1
      · exact le_iSup (fun i : Fin 3 => stdSimplex.face ({i}ᶜ : Finset (Fin 3))) 2
  exact h

lemma F₀_sup_I₁₂_eq_B₂ : F₀ ⊔ I₁₂ = B₂ := by
  calc F₀ ⊔ I₁₂ = F₀ ⊔ (F₂ ⊔ F₁) := rfl
    _ = F₀ ⊔ (F₁ ⊔ F₂) := by rw [sup_comm F₂ F₁]
    _ = (F₀ ⊔ F₁) ⊔ F₂ := by rw [sup_assoc]
    _ = B₂ := B₂_eq_sup.symm

lemma F₀_inf_I₁₂_eq_V₁₂ : F₀ ⊓ I₁₂ = V₁₂ := by
  calc F₀ ⊓ I₁₂ = I₁₂ ⊓ F₀ := by rw [inf_comm]
    _ = (F₂ ⊔ F₁) ⊓ F₀ := rfl
    _ = (F₂ ⊓ F₀) ⊔ (F₁ ⊓ F₀) := by
        rw [CategoryTheory.Subfunctor.max_min]
    _ = (F₀ ⊓ F₂) ⊔ (F₀ ⊓ F₁) := by
        rw [inf_comm F₂ F₀, inf_comm F₁ F₀]
    _ = V₁ ⊔ V₂ := by
        rw [F₀_inf_F₂_eq_V₁, F₀_inf_F₁_eq_V₂]
    _ = V₁₂ := rfl

theorem sq₁ : SSet.Subcomplex.BicartSq V₀ F₂ F₁ I₁₂ :=
  { sup_eq := rfl
    inf_eq := F₂_inf_F₁_eq_V₀ }

theorem sq₂ : SSet.Subcomplex.BicartSq V₁₂ F₀ I₁₂ B₂ :=
  { sup_eq := F₀_sup_I₁₂_eq_B₂
    inf_eq := F₀_inf_I₁₂_eq_V₁₂ }

theorem sqV : SSet.Subcomplex.BicartSq (⊥ : (Δ[2] : SSet.{u}).Subcomplex) V₁ V₂ V₁₂ :=
  { sup_eq := rfl
    inf_eq := by
      rw [V₁_inf_V₂_eq_bot] }

lemma isoV₀_ι : isoV₀.hom ≫ SSet.Subcomplex.ι V₀ =
    stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by decide
lemma isoV₁_ι : isoV₁.hom ≫ SSet.Subcomplex.ι V₁ =
    stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by decide
lemma isoV₂_ι : isoV₂.hom ≫ SSet.Subcomplex.ι V₂ =
    stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by decide

-- Universe-stable: `faceSingletonComplIso_hom_ι` is rfl at ambient `u`.
lemma isoF₀_hom_ι : isoF₀.hom ≫ SSet.Subcomplex.ι F₀ = stdSimplex.δ (0 : Fin 3) := rfl
lemma isoF₁_hom_ι : isoF₁.hom ≫ SSet.Subcomplex.ι F₁ = stdSimplex.δ (1 : Fin 3) := rfl
lemma isoF₂_hom_ι : isoF₂.hom ≫ SSet.Subcomplex.ι F₂ = stdSimplex.δ (2 : Fin 3) := rfl

lemma isoV₀_hom_F₂ : isoV₀.hom ≫ SSet.Subcomplex.homOfLE V₀_le_F₂ =
    stdSimplex.δ (1 : Fin 2) ≫ isoF₂.hom := by
  apply (cancel_mono (SSet.Subcomplex.ι F₂)).mp
  calc isoV₀.hom ≫ SSet.Subcomplex.homOfLE V₀_le_F₂ ≫ SSet.Subcomplex.ι F₂
      = isoV₀.hom ≫ (SSet.Subcomplex.homOfLE V₀_le_F₂ ≫ SSet.Subcomplex.ι F₂) := rfl
    _ = isoV₀.hom ≫ SSet.Subcomplex.ι V₀ := by
          rw [SSet.Subcomplex.homOfLE_ι]
    _ = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := isoV₀_ι
    _ = stdSimplex.δ (1 : Fin 2) ≫ (isoF₂.hom ≫ SSet.Subcomplex.ι F₂) := by
          rw [← isoF₂_hom_ι]
    _ = (stdSimplex.δ (1 : Fin 2) ≫ isoF₂.hom) ≫ SSet.Subcomplex.ι F₂ := by
          rw [← Category.assoc]

lemma isoV₀_hom_F₁ : isoV₀.hom ≫ SSet.Subcomplex.homOfLE V₀_le_F₁ =
    stdSimplex.δ (1 : Fin 2) ≫ isoF₁.hom := by
  apply (cancel_mono (SSet.Subcomplex.ι F₁)).mp
  calc isoV₀.hom ≫ SSet.Subcomplex.homOfLE V₀_le_F₁ ≫ SSet.Subcomplex.ι F₁
      = isoV₀.hom ≫ (SSet.Subcomplex.homOfLE V₀_le_F₁ ≫ SSet.Subcomplex.ι F₁) := rfl
    _ = isoV₀.hom ≫ SSet.Subcomplex.ι V₀ := by
          rw [SSet.Subcomplex.homOfLE_ι]
    _ = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := isoV₀_ι
    _ = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by decide
    _ = stdSimplex.δ (1 : Fin 2) ≫ (isoF₁.hom ≫ SSet.Subcomplex.ι F₁) := by
          rw [← isoF₁_hom_ι]
    _ = (stdSimplex.δ (1 : Fin 2) ≫ isoF₁.hom) ≫ SSet.Subcomplex.ι F₁ := by
          rw [← Category.assoc]

lemma isoV₁_hom_F₀ : isoV₁.hom ≫ SSet.Subcomplex.homOfLE V₁_le_F₀ =
    stdSimplex.δ (1 : Fin 2) ≫ isoF₀.hom := by
  apply (cancel_mono (SSet.Subcomplex.ι F₀)).mp
  calc isoV₁.hom ≫ SSet.Subcomplex.homOfLE V₁_le_F₀ ≫ SSet.Subcomplex.ι F₀
      = isoV₁.hom ≫ (SSet.Subcomplex.homOfLE V₁_le_F₀ ≫ SSet.Subcomplex.ι F₀) := rfl
    _ = isoV₁.hom ≫ SSet.Subcomplex.ι V₁ := by
          rw [SSet.Subcomplex.homOfLE_ι]
    _ = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := isoV₁_ι
    _ = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by decide
    _ = stdSimplex.δ (1 : Fin 2) ≫ (isoF₀.hom ≫ SSet.Subcomplex.ι F₀) := by
          rw [← isoF₀_hom_ι]
    _ = (stdSimplex.δ (1 : Fin 2) ≫ isoF₀.hom) ≫ SSet.Subcomplex.ι F₀ := by
          rw [← Category.assoc]

lemma isoV₁_hom_F₂ : isoV₁.hom ≫ SSet.Subcomplex.homOfLE V₁_le_F₂ =
    stdSimplex.δ (0 : Fin 2) ≫ isoF₂.hom := by
  apply (cancel_mono (SSet.Subcomplex.ι F₂)).mp
  calc isoV₁.hom ≫ SSet.Subcomplex.homOfLE V₁_le_F₂ ≫ SSet.Subcomplex.ι F₂
      = isoV₁.hom ≫ (SSet.Subcomplex.homOfLE V₁_le_F₂ ≫ SSet.Subcomplex.ι F₂) := rfl
    _ = isoV₁.hom ≫ SSet.Subcomplex.ι V₁ := by
          rw [SSet.Subcomplex.homOfLE_ι]
    _ = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := isoV₁_ι
    _ = stdSimplex.δ (0 : Fin 2) ≫ (isoF₂.hom ≫ SSet.Subcomplex.ι F₂) := by
          rw [← isoF₂_hom_ι]
    _ = (stdSimplex.δ (0 : Fin 2) ≫ isoF₂.hom) ≫ SSet.Subcomplex.ι F₂ := by
          rw [← Category.assoc]

lemma isoV₂_hom_F₀ : isoV₂.hom ≫ SSet.Subcomplex.homOfLE V₂_le_F₀ =
    stdSimplex.δ (0 : Fin 2) ≫ isoF₀.hom := by
  apply (cancel_mono (SSet.Subcomplex.ι F₀)).mp
  calc isoV₂.hom ≫ SSet.Subcomplex.homOfLE V₂_le_F₀ ≫ SSet.Subcomplex.ι F₀
      = isoV₂.hom ≫ (SSet.Subcomplex.homOfLE V₂_le_F₀ ≫ SSet.Subcomplex.ι F₀) := rfl
    _ = isoV₂.hom ≫ SSet.Subcomplex.ι V₂ := by
          rw [SSet.Subcomplex.homOfLE_ι]
    _ = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := isoV₂_ι
    _ = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by decide
    _ = stdSimplex.δ (0 : Fin 2) ≫ (isoF₀.hom ≫ SSet.Subcomplex.ι F₀) := by
          rw [← isoF₀_hom_ι]
    _ = (stdSimplex.δ (0 : Fin 2) ≫ isoF₀.hom) ≫ SSet.Subcomplex.ι F₀ := by
          rw [← Category.assoc]

lemma isoV₂_hom_F₁ : isoV₂.hom ≫ SSet.Subcomplex.homOfLE V₂_le_F₁ =
    stdSimplex.δ (0 : Fin 2) ≫ isoF₁.hom := by
  apply (cancel_mono (SSet.Subcomplex.ι F₁)).mp
  calc isoV₂.hom ≫ SSet.Subcomplex.homOfLE V₂_le_F₁ ≫ SSet.Subcomplex.ι F₁
      = isoV₂.hom ≫ (SSet.Subcomplex.homOfLE V₂_le_F₁ ≫ SSet.Subcomplex.ι F₁) := rfl
    _ = isoV₂.hom ≫ SSet.Subcomplex.ι V₂ := by
          rw [SSet.Subcomplex.homOfLE_ι]
    _ = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := isoV₂_ι
    _ = stdSimplex.δ (0 : Fin 2) ≫ (isoF₁.hom ≫ SSet.Subcomplex.ι F₁) := by
          rw [← isoF₁_hom_ι]
    _ = (stdSimplex.δ (0 : Fin 2) ≫ isoF₁.hom) ≫ SSet.Subcomplex.ι F₁ := by
          rw [← Category.assoc]

lemma homOfLE_V₀_F₂_inv : SSet.Subcomplex.homOfLE V₀_le_F₂ ≫ isoF₂.inv =
    isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) := by
  have h : isoV₀.hom ≫ SSet.Subcomplex.homOfLE V₀_le_F₂ = stdSimplex.δ (1 : Fin 2) ≫ isoF₂.hom :=
    isoV₀_hom_F₂
  calc SSet.Subcomplex.homOfLE V₀_le_F₂ ≫ isoF₂.inv
      = 𝟙 _ ≫ (SSet.Subcomplex.homOfLE V₀_le_F₂ ≫ isoF₂.inv) := by rw [Category.id_comp]
    _ = (isoV₀.inv ≫ isoV₀.hom) ≫ (SSet.Subcomplex.homOfLE V₀_le_F₂ ≫ isoF₂.inv) := by
        rw [Iso.inv_hom_id]
    _ = isoV₀.inv ≫ (isoV₀.hom ≫ SSet.Subcomplex.homOfLE V₀_le_F₂) ≫ isoF₂.inv := by
        simp only [Category.assoc]
    _ = isoV₀.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫ isoF₂.hom) ≫ isoF₂.inv := by rw [h]
    _ = isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ (isoF₂.hom ≫ isoF₂.inv) := by
        simp only [Category.assoc]
    _ = isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) := by
        simp only [Iso.hom_inv_id, Category.comp_id]

lemma homOfLE_V₀_F₁_inv : SSet.Subcomplex.homOfLE V₀_le_F₁ ≫ isoF₁.inv =
    isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) := by
  have h : isoV₀.hom ≫ SSet.Subcomplex.homOfLE V₀_le_F₁ = stdSimplex.δ (1 : Fin 2) ≫ isoF₁.hom :=
    isoV₀_hom_F₁
  calc SSet.Subcomplex.homOfLE V₀_le_F₁ ≫ isoF₁.inv
      = 𝟙 _ ≫ (SSet.Subcomplex.homOfLE V₀_le_F₁ ≫ isoF₁.inv) := by rw [Category.id_comp]
    _ = (isoV₀.inv ≫ isoV₀.hom) ≫ (SSet.Subcomplex.homOfLE V₀_le_F₁ ≫ isoF₁.inv) := by
        rw [Iso.inv_hom_id]
    _ = isoV₀.inv ≫ (isoV₀.hom ≫ SSet.Subcomplex.homOfLE V₀_le_F₁) ≫ isoF₁.inv := by
        simp only [Category.assoc]
    _ = isoV₀.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫ isoF₁.hom) ≫ isoF₁.inv := by rw [h]
    _ = isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ (isoF₁.hom ≫ isoF₁.inv) := by
        simp only [Category.assoc]
    _ = isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) := by
        simp only [Iso.hom_inv_id, Category.comp_id]

lemma homOfLE_V₁_F₀_inv : SSet.Subcomplex.homOfLE V₁_le_F₀ ≫ isoF₀.inv =
    isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2) := by
  have h := isoV₁_hom_F₀
  calc SSet.Subcomplex.homOfLE V₁_le_F₀ ≫ isoF₀.inv
      = 𝟙 _ ≫ (SSet.Subcomplex.homOfLE V₁_le_F₀ ≫ isoF₀.inv) := by rw [Category.id_comp]
    _ = (isoV₁.inv ≫ isoV₁.hom) ≫ (SSet.Subcomplex.homOfLE V₁_le_F₀ ≫ isoF₀.inv) := by
        rw [Iso.inv_hom_id]
    _ = isoV₁.inv ≫ (isoV₁.hom ≫ SSet.Subcomplex.homOfLE V₁_le_F₀) ≫ isoF₀.inv := by
        simp only [Category.assoc]
    _ = isoV₁.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫ isoF₀.hom) ≫ isoF₀.inv := by rw [h]
    _ = isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma homOfLE_V₁_F₂_inv : SSet.Subcomplex.homOfLE V₁_le_F₂ ≫ isoF₂.inv =
    isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2) := by
  have h := isoV₁_hom_F₂
  calc SSet.Subcomplex.homOfLE V₁_le_F₂ ≫ isoF₂.inv
      = 𝟙 _ ≫ (SSet.Subcomplex.homOfLE V₁_le_F₂ ≫ isoF₂.inv) := by rw [Category.id_comp]
    _ = (isoV₁.inv ≫ isoV₁.hom) ≫ (SSet.Subcomplex.homOfLE V₁_le_F₂ ≫ isoF₂.inv) := by
        rw [Iso.inv_hom_id]
    _ = isoV₁.inv ≫ (isoV₁.hom ≫ SSet.Subcomplex.homOfLE V₁_le_F₂) ≫ isoF₂.inv := by
        simp only [Category.assoc]
    _ = isoV₁.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫ isoF₂.hom) ≫ isoF₂.inv := by rw [h]
    _ = isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma homOfLE_V₂_F₀_inv : SSet.Subcomplex.homOfLE V₂_le_F₀ ≫ isoF₀.inv =
    isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) := by
  have h := isoV₂_hom_F₀
  calc SSet.Subcomplex.homOfLE V₂_le_F₀ ≫ isoF₀.inv
      = 𝟙 _ ≫ (SSet.Subcomplex.homOfLE V₂_le_F₀ ≫ isoF₀.inv) := by rw [Category.id_comp]
    _ = (isoV₂.inv ≫ isoV₂.hom) ≫ (SSet.Subcomplex.homOfLE V₂_le_F₀ ≫ isoF₀.inv) := by
        rw [Iso.inv_hom_id]
    _ = isoV₂.inv ≫ (isoV₂.hom ≫ SSet.Subcomplex.homOfLE V₂_le_F₀) ≫ isoF₀.inv := by
        simp only [Category.assoc]
    _ = isoV₂.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫ isoF₀.hom) ≫ isoF₀.inv := by rw [h]
    _ = isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma homOfLE_V₂_F₁_inv : SSet.Subcomplex.homOfLE V₂_le_F₁ ≫ isoF₁.inv =
    isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) := by
  have h := isoV₂_hom_F₁
  calc SSet.Subcomplex.homOfLE V₂_le_F₁ ≫ isoF₁.inv
      = 𝟙 _ ≫ (SSet.Subcomplex.homOfLE V₂_le_F₁ ≫ isoF₁.inv) := by rw [Category.id_comp]
    _ = (isoV₂.inv ≫ isoV₂.hom) ≫ (SSet.Subcomplex.homOfLE V₂_le_F₁ ≫ isoF₁.inv) := by
        rw [Iso.inv_hom_id]
    _ = isoV₂.inv ≫ (isoV₂.hom ≫ SSet.Subcomplex.homOfLE V₂_le_F₁) ≫ isoF₁.inv := by
        simp only [Category.assoc]
    _ = isoV₂.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫ isoF₁.hom) ≫ isoF₁.inv := by rw [h]
    _ = isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma boundary_ι_zero_eq :
    SSet.boundary.ι (0 : Fin 3) = isoF₀.hom ≫ SSet.Subcomplex.homOfLE F₀_le_B₂ := by
  apply (cancel_mono (SSet.Subcomplex.ι B₂)).mp
  calc SSet.boundary.ι (0 : Fin 3) ≫ SSet.Subcomplex.ι B₂
      = stdSimplex.δ (0 : Fin 3) := rfl
    _ = isoF₀.hom ≫ SSet.Subcomplex.ι F₀ := rfl
    _ = isoF₀.hom ≫ (SSet.Subcomplex.homOfLE F₀_le_B₂ ≫ SSet.Subcomplex.ι B₂) := by
          rw [← SSet.Subcomplex.homOfLE_ι]
    _ = (isoF₀.hom ≫ SSet.Subcomplex.homOfLE F₀_le_B₂) ≫ SSet.Subcomplex.ι B₂ := by
          rw [← Category.assoc]

lemma boundary_ι_one_eq :
    SSet.boundary.ι (1 : Fin 3) = isoF₁.hom ≫ SSet.Subcomplex.homOfLE F₁_le_B₂ := by
  apply (cancel_mono (SSet.Subcomplex.ι B₂)).mp
  calc SSet.boundary.ι (1 : Fin 3) ≫ SSet.Subcomplex.ι B₂
      = stdSimplex.δ (1 : Fin 3) := rfl
    _ = isoF₁.hom ≫ SSet.Subcomplex.ι F₁ := rfl
    _ = isoF₁.hom ≫ (SSet.Subcomplex.homOfLE F₁_le_B₂ ≫ SSet.Subcomplex.ι B₂) := by
          rw [← SSet.Subcomplex.homOfLE_ι]
    _ = (isoF₁.hom ≫ SSet.Subcomplex.homOfLE F₁_le_B₂) ≫ SSet.Subcomplex.ι B₂ := by
          rw [← Category.assoc]

lemma boundary_ι_two_eq :
    SSet.boundary.ι (2 : Fin 3) = isoF₂.hom ≫ SSet.Subcomplex.homOfLE F₂_le_B₂ := by
  apply (cancel_mono (SSet.Subcomplex.ι B₂)).mp
  calc SSet.boundary.ι (2 : Fin 3) ≫ SSet.Subcomplex.ι B₂
      = stdSimplex.δ (2 : Fin 3) := rfl
    _ = isoF₂.hom ≫ SSet.Subcomplex.ι F₂ := rfl
    _ = isoF₂.hom ≫ (SSet.Subcomplex.homOfLE F₂_le_B₂ ≫ SSet.Subcomplex.ι B₂) := by
          rw [← SSet.Subcomplex.homOfLE_ι]
    _ = (isoF₂.hom ≫ SSet.Subcomplex.homOfLE F₂_le_B₂) ≫ SSet.Subcomplex.ι B₂ := by
          rw [← Category.assoc]

lemma homOfLE_F₁_le_B₂_eq :
    SSet.Subcomplex.homOfLE F₁_le_B₂ =
    SSet.Subcomplex.homOfLE F₁_le_I₁₂ ≫ SSet.Subcomplex.homOfLE I₁₂_le_B₂ := rfl

lemma homOfLE_F₂_le_B₂_eq :
    SSet.Subcomplex.homOfLE F₂_le_B₂ =
    SSet.Subcomplex.homOfLE F₂_le_I₁₂ ≫ SSet.Subcomplex.homOfLE I₁₂_le_B₂ := rfl

end Impl

/-- Reusable gluing of three compatible edges to a map `∂Δ[2] → X`.

The three edges are `e₀₁ : Δ[1] → X` (edge `0–1`), `e₀₂ : Δ[1] → X`
(edge `0–2`), `e₁₂ : Δ[1] → X` (edge `1–2`).  The three
compatibilities are the vertex equalities

* `δ₁ ≫ e₀₁ = δ₁ ≫ e₀₂` (vertex `0`),
* `δ₀ ≫ e₀₁ = δ₁ ≫ e₁₂` (vertex `1`),
* `δ₀ ≫ e₀₂ = δ₀ ≫ e₁₂` (vertex `2`),

where `δ₀, δ₁ : Δ[0] → Δ[1]` are the two face inclusions.
The resulting map `twoDesc e₀₁ e₀₂ e₁₂` satisfies

* `boundary.ι 0 ≫ twoDesc = e₁₂` (face `0`, i.e. edge `1–2`),
* `boundary.ι 1 ≫ twoDesc = e₀₂` (face `1`, i.e. edge `0–2`),
* `boundary.ι 2 ≫ twoDesc = e₀₁` (face `2`, i.e. edge `0–1`),

in the orientation `face {i}ᶜ` opposite vertex `i`.
The construction is the two-step `BicartSq.isPushout` gluing
`Λ[2,0] = F₂ ⊔ F₁` then `∂Δ[2] = F₀ ⊔ Λ[2,0]`.
-/
noncomputable def twoDesc
    (e₀₁ e₀₂ e₁₂ : Δ[1] ⟶ X)
    (h₀ : stdSimplex.δ (1 : Fin 2) ≫ e₀₁ = stdSimplex.δ (1 : Fin 2) ≫ e₀₂)
    (h₁ : stdSimplex.δ (0 : Fin 2) ≫ e₀₁ = stdSimplex.δ (1 : Fin 2) ≫ e₁₂)
    (h₂ : stdSimplex.δ (0 : Fin 2) ≫ e₀₂ = stdSimplex.δ (0 : Fin 2) ≫ e₁₂) :
    (∂Δ[2] : SSet.{u}) ⟶ X := by
  let mapF₀' : (Impl.F₀ : SSet.{u}) ⟶ X := Impl.isoF₀.inv ≫ e₁₂
  let mapF₁' : (Impl.F₁ : SSet.{u}) ⟶ X := Impl.isoF₁.inv ≫ e₀₂
  let mapF₂' : (Impl.F₂ : SSet.{u}) ⟶ X := Impl.isoF₂.inv ≫ e₀₁
  let hPush₁ := SSet.Subcomplex.BicartSq.isPushout Impl.sq₁
  have hAgree₁ : SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ mapF₂' =
      SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ mapF₁' := by
    calc SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ mapF₂'
        = (SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ Impl.isoF₂.inv) ≫ e₀₁ := by
            rw [← Category.assoc]
      _ = (Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₀₁ := by
            rw [Impl.homOfLE_V₀_F₂_inv]
      _ = Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₀₁ := by
            rw [Category.assoc]
      _ = Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₀₂ := by rw [h₀]
      _ = (Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₀₂ := by
            rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ Impl.isoF₁.inv) ≫ e₀₂ := by
            rw [Impl.homOfLE_V₀_F₁_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ mapF₁' := by
            rw [← Category.assoc]
  let mapI₁₂' : (Impl.I₁₂ : SSet.{u}) ⟶ X := hPush₁.desc mapF₂' mapF₁' hAgree₁
  have hF₂_desc : SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' = mapF₂' :=
    hPush₁.inl_desc mapF₂' mapF₁' hAgree₁
  have hF₁_desc : SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' = mapF₁' :=
    hPush₁.inr_desc mapF₂' mapF₁' hAgree₁
  have hV₁_F₀ : SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := by
    calc SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀'
        = (SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ Impl.isoF₀.inv) ≫ e₁₂ := by
            rw [← Category.assoc]
      _ = (Impl.isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₁₂ := by
            rw [Impl.homOfLE_V₁_F₀_inv]
      _ = Impl.isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₁₂ := by
            rw [Category.assoc]
      _ = Impl.isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₀₁ := by rw [← h₁]
      _ = (Impl.isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₀₁ := by
            rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ Impl.isoF₂.inv) ≫ e₀₁ := by
            rw [Impl.homOfLE_V₁_F₂_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := by
            rw [← Category.assoc]
  have hV₂_F₀ : SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := by
    calc SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀'
        = (SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ Impl.isoF₀.inv) ≫ e₁₂ := by
            rw [← Category.assoc]
      _ = (Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₁₂ := by
            rw [Impl.homOfLE_V₂_F₀_inv]
      _ = Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₁₂ := by
            rw [Category.assoc]
      _ = Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₀₂ := by rw [← h₂]
      _ = (Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₀₂ := by
            rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ Impl.isoF₁.inv) ≫ e₀₂ := by
            rw [Impl.homOfLE_V₂_F₁_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := by
            rw [← Category.assoc]
  have hPushV := SSet.Subcomplex.BicartSq.isPushout Impl.sqV
  have hAgree₂ :
      SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
    apply hPushV.hom_ext
    · calc SSet.Subcomplex.homOfLE Impl.V₁_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀'
          = SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := hV₁_F₀
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫
            SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [hF₂_desc.symm]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc, SSet.Subcomplex.homOfLE_comp_assoc]
    · calc SSet.Subcomplex.homOfLE Impl.V₂_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀'
          = SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := hV₂_F₀
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫
            SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' := by
            rw [hF₁_desc.symm]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc, SSet.Subcomplex.homOfLE_comp_assoc]
  let hPush₂ := SSet.Subcomplex.BicartSq.isPushout Impl.sq₂
  exact hPush₂.desc mapF₀' mapI₁₂' hAgree₂

@[reassoc (attr := simp)]
lemma twoDesc_ι_zero {e₀₁ e₀₂ e₁₂ : Δ[1] ⟶ X}
    (h₀ : stdSimplex.δ (1 : Fin 2) ≫ e₀₁ = stdSimplex.δ (1 : Fin 2) ≫ e₀₂)
    (h₁ : stdSimplex.δ (0 : Fin 2) ≫ e₀₁ = stdSimplex.δ (1 : Fin 2) ≫ e₁₂)
    (h₂ : stdSimplex.δ (0 : Fin 2) ≫ e₀₂ = stdSimplex.δ (0 : Fin 2) ≫ e₁₂) :
    SSet.boundary.ι (0 : Fin 3) ≫ twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ = e₁₂ := by
  -- reuse Impl static helpers; dynamic part matches `twoDesc`
  let mapF₀' : (Impl.F₀ : SSet.{u}) ⟶ X := Impl.isoF₀.inv ≫ e₁₂
  let mapF₁' : (Impl.F₁ : SSet.{u}) ⟶ X := Impl.isoF₁.inv ≫ e₀₂
  let mapF₂' : (Impl.F₂ : SSet.{u}) ⟶ X := Impl.isoF₂.inv ≫ e₀₁
  let hPush₁ := SSet.Subcomplex.BicartSq.isPushout Impl.sq₁
  have hAgree₁ : SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ mapF₂' =
      SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ mapF₁' := by
    calc SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ mapF₂'
        = (SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ Impl.isoF₂.inv) ≫ e₀₁ := by
            rw [← Category.assoc]
      _ = (Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₀₁ := by
            rw [Impl.homOfLE_V₀_F₂_inv]
      _ = Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₀₁ := by
            rw [Category.assoc]
      _ = Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₀₂ := by rw [h₀]
      _ = (Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₀₂ := by
            rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ Impl.isoF₁.inv) ≫ e₀₂ := by
            rw [Impl.homOfLE_V₀_F₁_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ mapF₁' := by
            rw [← Category.assoc]
  let mapI₁₂' : (Impl.I₁₂ : SSet.{u}) ⟶ X := hPush₁.desc mapF₂' mapF₁' hAgree₁
  have hV₁_F₀ : SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := by
    calc SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀'
        = (SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ Impl.isoF₀.inv) ≫ e₁₂ := by
            rw [← Category.assoc]
      _ = (Impl.isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₁₂ := by
            rw [Impl.homOfLE_V₁_F₀_inv]
      _ = Impl.isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₁₂ := by
            rw [Category.assoc]
      _ = Impl.isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₀₁ := by rw [← h₁]
      _ = (Impl.isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₀₁ := by
            rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ Impl.isoF₂.inv) ≫ e₀₁ := by
            rw [Impl.homOfLE_V₁_F₂_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := by
            rw [← Category.assoc]
  have hV₂_F₀ : SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := by
    calc SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀'
        = (SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ Impl.isoF₀.inv) ≫ e₁₂ := by
            rw [← Category.assoc]
      _ = (Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₁₂ := by
            rw [Impl.homOfLE_V₂_F₀_inv]
      _ = Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₁₂ := by
            rw [Category.assoc]
      _ = Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₀₂ := by rw [← h₂]
      _ = (Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₀₂ := by
            rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ Impl.isoF₁.inv) ≫ e₀₂ := by
            rw [Impl.homOfLE_V₂_F₁_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := by
            rw [← Category.assoc]
  have hF₂_desc : SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' = mapF₂' :=
    hPush₁.inl_desc mapF₂' mapF₁' hAgree₁
  have hF₁_desc : SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' = mapF₁' :=
    hPush₁.inr_desc mapF₂' mapF₁' hAgree₁
  have hPushV := SSet.Subcomplex.BicartSq.isPushout Impl.sqV
  have hAgree₂ :
      SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
    apply hPushV.hom_ext
    · calc SSet.Subcomplex.homOfLE Impl.V₁_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀'
          = SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := hV₁_F₀
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫
            SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [hF₂_desc.symm]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc, SSet.Subcomplex.homOfLE_comp_assoc]
    · calc SSet.Subcomplex.homOfLE Impl.V₂_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀'
          = SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := hV₂_F₀
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫
            SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' := by
            rw [hF₁_desc.symm]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc, SSet.Subcomplex.homOfLE_comp_assoc]
  let hPush₂ := SSet.Subcomplex.BicartSq.isPushout Impl.sq₂
  have hTwoDesc : twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ =
      hPush₂.desc mapF₀' mapI₁₂' hAgree₂ := rfl
  have hF₀_desc : SSet.Subcomplex.homOfLE Impl.F₀_le_B₂ ≫
      hPush₂.desc mapF₀' mapI₁₂' hAgree₂ = mapF₀' :=
    hPush₂.inl_desc mapF₀' mapI₁₂' hAgree₂
  calc SSet.boundary.ι (0 : Fin 3) ≫ twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂
      = (Impl.isoF₀.hom ≫ SSet.Subcomplex.homOfLE Impl.F₀_le_B₂) ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by
          rw [Impl.boundary_ι_zero_eq]
    _ = Impl.isoF₀.hom ≫ SSet.Subcomplex.homOfLE Impl.F₀_le_B₂ ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Category.assoc]
    _ = Impl.isoF₀.hom ≫ SSet.Subcomplex.homOfLE Impl.F₀_le_B₂ ≫
          hPush₂.desc mapF₀' mapI₁₂' hAgree₂ := by rw [hTwoDesc]
    _ = Impl.isoF₀.hom ≫ mapF₀' := by
          rw [hF₀_desc]
    _ = e₁₂ := by
          calc Impl.isoF₀.hom ≫ mapF₀'
              = Impl.isoF₀.hom ≫ (Impl.isoF₀.inv ≫ e₁₂) := rfl
            _ = (Impl.isoF₀.hom ≫ Impl.isoF₀.inv) ≫ e₁₂ := by rw [Category.assoc]
            _ = e₁₂ := by rw [Iso.hom_inv_id, Category.id_comp]

@[reassoc (attr := simp)]
lemma twoDesc_ι_one {e₀₁ e₀₂ e₁₂ : Δ[1] ⟶ X}
    (h₀ : stdSimplex.δ (1 : Fin 2) ≫ e₀₁ = stdSimplex.δ (1 : Fin 2) ≫ e₀₂)
    (h₁ : stdSimplex.δ (0 : Fin 2) ≫ e₀₁ = stdSimplex.δ (1 : Fin 2) ≫ e₁₂)
    (h₂ : stdSimplex.δ (0 : Fin 2) ≫ e₀₂ = stdSimplex.δ (0 : Fin 2) ≫ e₁₂) :
    SSet.boundary.ι (1 : Fin 3) ≫ twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ = e₀₂ := by
  let mapF₀' : (Impl.F₀ : SSet.{u}) ⟶ X := Impl.isoF₀.inv ≫ e₁₂
  let mapF₁' : (Impl.F₁ : SSet.{u}) ⟶ X := Impl.isoF₁.inv ≫ e₀₂
  let mapF₂' : (Impl.F₂ : SSet.{u}) ⟶ X := Impl.isoF₂.inv ≫ e₀₁
  let hPush₁ := SSet.Subcomplex.BicartSq.isPushout Impl.sq₁
  have hAgree₁ : SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ mapF₂' =
      SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ mapF₁' := by
    calc SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ mapF₂'
        = (SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ Impl.isoF₂.inv) ≫ e₀₁ := by
            rw [← Category.assoc]
      _ = (Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₀₁ := by
            rw [Impl.homOfLE_V₀_F₂_inv]
      _ = Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₀₁ := by rw [Category.assoc]
      _ = Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₀₂ := by rw [h₀]
      _ = (Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₀₂ := by rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ Impl.isoF₁.inv) ≫ e₀₂ := by
            rw [Impl.homOfLE_V₀_F₁_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ mapF₁' := by rw [← Category.assoc]
  let mapI₁₂' : (Impl.I₁₂ : SSet.{u}) ⟶ X := hPush₁.desc mapF₂' mapF₁' hAgree₁
  have hF₂_desc : SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' = mapF₂' :=
    hPush₁.inl_desc mapF₂' mapF₁' hAgree₁
  have hF₁_desc : SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' = mapF₁' :=
    hPush₁.inr_desc mapF₂' mapF₁' hAgree₁
  have hV₁_F₀ : SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := by
    calc SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀'
        = (SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ Impl.isoF₀.inv) ≫ e₁₂ := by rw [← Category.assoc]
      _ = (Impl.isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₁₂ := by rw [Impl.homOfLE_V₁_F₀_inv]
      _ = Impl.isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₁₂ := by rw [Category.assoc]
      _ = Impl.isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₀₁ := by rw [← h₁]
      _ = (Impl.isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₀₁ := by rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ Impl.isoF₂.inv) ≫ e₀₁ :=
        by rw [Impl.homOfLE_V₁_F₂_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := by rw [← Category.assoc]
  have hV₂_F₀ : SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := by
    calc SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀'
        = (SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ Impl.isoF₀.inv) ≫ e₁₂ := by rw [← Category.assoc]
      _ = (Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₁₂ := by rw [Impl.homOfLE_V₂_F₀_inv]
      _ = Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₁₂ := by rw [Category.assoc]
      _ = Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₀₂ := by rw [← h₂]
      _ = (Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₀₂ := by rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ Impl.isoF₁.inv) ≫ e₀₂ :=
        by rw [Impl.homOfLE_V₂_F₁_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := by rw [← Category.assoc]
  have hPushV := SSet.Subcomplex.BicartSq.isPushout Impl.sqV
  have hAgree₂ :
      SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
    apply hPushV.hom_ext
    · calc SSet.Subcomplex.homOfLE Impl.V₁_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀'
          = SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := hV₁_F₀
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫
            SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [hF₂_desc.symm]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc, SSet.Subcomplex.homOfLE_comp_assoc]
    · calc SSet.Subcomplex.homOfLE Impl.V₂_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀'
          = SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := hV₂_F₀
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫
            SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' := by
            rw [hF₁_desc.symm]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc, SSet.Subcomplex.homOfLE_comp_assoc]
  let hPush₂ := SSet.Subcomplex.BicartSq.isPushout Impl.sq₂
  have hTwoDesc : twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ = hPush₂.desc mapF₀' mapI₁₂' hAgree₂ := rfl
  have hI₁₂_desc : SSet.Subcomplex.homOfLE Impl.I₁₂_le_B₂ ≫ hPush₂.desc mapF₀' mapI₁₂' hAgree₂ =
    mapI₁₂' :=
    hPush₂.inr_desc mapF₀' mapI₁₂' hAgree₂
  calc SSet.boundary.ι (1 : Fin 3) ≫ twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂
      = (Impl.isoF₁.hom ≫ SSet.Subcomplex.homOfLE Impl.F₁_le_B₂) ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Impl.boundary_ι_one_eq]
    _ = Impl.isoF₁.hom ≫ SSet.Subcomplex.homOfLE Impl.F₁_le_B₂ ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Category.assoc]
    _ = Impl.isoF₁.hom ≫
          (SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ SSet.Subcomplex.homOfLE Impl.I₁₂_le_B₂) ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Impl.homOfLE_F₁_le_B₂_eq]
    _ = Impl.isoF₁.hom ≫ SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫
          SSet.Subcomplex.homOfLE Impl.I₁₂_le_B₂ ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Category.assoc]
    _ = Impl.isoF₁.hom ≫ SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫
          SSet.Subcomplex.homOfLE Impl.I₁₂_le_B₂ ≫
          hPush₂.desc mapF₀' mapI₁₂' hAgree₂ := by rw [hTwoDesc]
    _ = Impl.isoF₁.hom ≫ SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' := by
          rw [hI₁₂_desc]
    _ = Impl.isoF₁.hom ≫ mapF₁' := by rw [hF₁_desc]
    _ = e₀₂ := by
          calc Impl.isoF₁.hom ≫ mapF₁'
              = Impl.isoF₁.hom ≫ (Impl.isoF₁.inv ≫ e₀₂) := rfl
            _ = (Impl.isoF₁.hom ≫ Impl.isoF₁.inv) ≫ e₀₂ := by rw [Category.assoc]
            _ = e₀₂ := by rw [Iso.hom_inv_id, Category.id_comp]

@[reassoc (attr := simp)]
lemma twoDesc_ι_two {e₀₁ e₀₂ e₁₂ : Δ[1] ⟶ X}
    (h₀ : stdSimplex.δ (1 : Fin 2) ≫ e₀₁ = stdSimplex.δ (1 : Fin 2) ≫ e₀₂)
    (h₁ : stdSimplex.δ (0 : Fin 2) ≫ e₀₁ = stdSimplex.δ (1 : Fin 2) ≫ e₁₂)
    (h₂ : stdSimplex.δ (0 : Fin 2) ≫ e₀₂ = stdSimplex.δ (0 : Fin 2) ≫ e₁₂) :
    SSet.boundary.ι (2 : Fin 3) ≫ twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ = e₀₁ := by
  let mapF₀' : (Impl.F₀ : SSet.{u}) ⟶ X := Impl.isoF₀.inv ≫ e₁₂
  let mapF₁' : (Impl.F₁ : SSet.{u}) ⟶ X := Impl.isoF₁.inv ≫ e₀₂
  let mapF₂' : (Impl.F₂ : SSet.{u}) ⟶ X := Impl.isoF₂.inv ≫ e₀₁
  let hPush₁ := SSet.Subcomplex.BicartSq.isPushout Impl.sq₁
  have hAgree₁ : SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ mapF₂' =
      SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ mapF₁' := by
    calc SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ mapF₂'
        = (SSet.Subcomplex.homOfLE Impl.V₀_le_F₂ ≫ Impl.isoF₂.inv) ≫ e₀₁ := by rw [← Category.assoc]
      _ = (Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₀₁ := by rw [Impl.homOfLE_V₀_F₂_inv]
      _ = Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₀₁ := by rw [Category.assoc]
      _ = Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₀₂ := by rw [h₀]
      _ = (Impl.isoV₀.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₀₂ := by rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ Impl.isoF₁.inv) ≫ e₀₂ :=
        by rw [Impl.homOfLE_V₀_F₁_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₀_le_F₁ ≫ mapF₁' := by rw [← Category.assoc]
  let mapI₁₂' : (Impl.I₁₂ : SSet.{u}) ⟶ X := hPush₁.desc mapF₂' mapF₁' hAgree₁
  have hF₂_desc : SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' = mapF₂' :=
    hPush₁.inl_desc mapF₂' mapF₁' hAgree₁
  have hF₁_desc : SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' = mapF₁' :=
    hPush₁.inr_desc mapF₂' mapF₁' hAgree₁
  have hV₁_F₀ : SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := by
    calc SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀'
        = (SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ Impl.isoF₀.inv) ≫ e₁₂ := by rw [← Category.assoc]
      _ = (Impl.isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2)) ≫ e₁₂ := by rw [Impl.homOfLE_V₁_F₀_inv]
      _ = Impl.isoV₁.inv ≫ stdSimplex.δ (1 : Fin 2) ≫ e₁₂ := by rw [Category.assoc]
      _ = Impl.isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₀₁ := by rw [← h₁]
      _ = (Impl.isoV₁.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₀₁ := by rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ Impl.isoF₂.inv) ≫ e₀₁ :=
        by rw [Impl.homOfLE_V₁_F₂_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := by rw [← Category.assoc]
  have hV₂_F₀ : SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := by
    calc SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀'
        = (SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ Impl.isoF₀.inv) ≫ e₁₂ := by rw [← Category.assoc]
      _ = (Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₁₂ := by rw [Impl.homOfLE_V₂_F₀_inv]
      _ = Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₁₂ := by rw [Category.assoc]
      _ = Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2) ≫ e₀₂ := by rw [← h₂]
      _ = (Impl.isoV₂.inv ≫ stdSimplex.δ (0 : Fin 2)) ≫ e₀₂ := by rw [← Category.assoc]
      _ = (SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ Impl.isoF₁.inv) ≫ e₀₂ :=
        by rw [Impl.homOfLE_V₂_F₁_inv]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := by rw [← Category.assoc]
  have hPushV := SSet.Subcomplex.BicartSq.isPushout Impl.sqV
  have hAgree₂ :
      SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀' =
      SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
    apply hPushV.hom_ext
    · calc SSet.Subcomplex.homOfLE Impl.V₁_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀'
          = SSet.Subcomplex.homOfLE Impl.V₁_le_F₀ ≫ mapF₀' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫ mapF₂' := hV₁_F₀
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_F₂ ≫
            SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [hF₂_desc.symm]
      _ = SSet.Subcomplex.homOfLE Impl.V₁_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc, SSet.Subcomplex.homOfLE_comp_assoc]
    · calc SSet.Subcomplex.homOfLE Impl.V₂_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_F₀ ≫ mapF₀'
          = SSet.Subcomplex.homOfLE Impl.V₂_le_F₀ ≫ mapF₀' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫ mapF₁' := hV₂_F₀
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_F₁ ≫
            SSet.Subcomplex.homOfLE Impl.F₁_le_I₁₂ ≫ mapI₁₂' := by
            rw [hF₁_desc.symm]
      _ = SSet.Subcomplex.homOfLE Impl.V₂_le_V₁₂ ≫
            SSet.Subcomplex.homOfLE Impl.V₁₂_le_I₁₂ ≫ mapI₁₂' := by
            rw [SSet.Subcomplex.homOfLE_comp_assoc, SSet.Subcomplex.homOfLE_comp_assoc]
  let hPush₂ := SSet.Subcomplex.BicartSq.isPushout Impl.sq₂
  have hTwoDesc : twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ = hPush₂.desc mapF₀' mapI₁₂' hAgree₂ := rfl
  have hI₁₂_desc : SSet.Subcomplex.homOfLE Impl.I₁₂_le_B₂ ≫ hPush₂.desc mapF₀' mapI₁₂' hAgree₂ =
    mapI₁₂' :=
    hPush₂.inr_desc mapF₀' mapI₁₂' hAgree₂
  calc SSet.boundary.ι (2 : Fin 3) ≫ twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂
      = (Impl.isoF₂.hom ≫ SSet.Subcomplex.homOfLE Impl.F₂_le_B₂) ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Impl.boundary_ι_two_eq]
    _ = Impl.isoF₂.hom ≫ SSet.Subcomplex.homOfLE Impl.F₂_le_B₂ ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Category.assoc]
    _ = Impl.isoF₂.hom ≫
          (SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ SSet.Subcomplex.homOfLE Impl.I₁₂_le_B₂) ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Impl.homOfLE_F₂_le_B₂_eq]
    _ = Impl.isoF₂.hom ≫ SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫
          SSet.Subcomplex.homOfLE Impl.I₁₂_le_B₂ ≫
          twoDesc (X := X) e₀₁ e₀₂ e₁₂ h₀ h₁ h₂ := by rw [Category.assoc]
    _ = Impl.isoF₂.hom ≫ SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫
          SSet.Subcomplex.homOfLE Impl.I₁₂_le_B₂ ≫
          hPush₂.desc mapF₀' mapI₁₂' hAgree₂ := by rw [hTwoDesc]
    _ = Impl.isoF₂.hom ≫ SSet.Subcomplex.homOfLE Impl.F₂_le_I₁₂ ≫ mapI₁₂' := by
          rw [hI₁₂_desc]
    _ = Impl.isoF₂.hom ≫ mapF₂' := by rw [hF₂_desc]
    _ = e₀₁ := by
          calc Impl.isoF₂.hom ≫ mapF₂'
              = Impl.isoF₂.hom ≫ (Impl.isoF₂.inv ≫ e₀₁) := rfl
            _ = (Impl.isoF₂.hom ≫ Impl.isoF₂.inv) ≫ e₀₁ := by rw [Category.assoc]
            _ = e₀₁ := by rw [Iso.hom_inv_id, Category.id_comp]

theorem hom_ext_two {f g : (∂Δ[2] : SSet.{u}) ⟶ X}
    (h0 : SSet.boundary.ι (0 : Fin 3) ≫ f = SSet.boundary.ι (0 : Fin 3) ≫ g)
    (h1 : SSet.boundary.ι (1 : Fin 3) ≫ f = SSet.boundary.ι (1 : Fin 3) ≫ g)
    (h2 : SSet.boundary.ι (2 : Fin 3) ≫ f = SSet.boundary.ι (2 : Fin 3) ≫ g) :
    f = g := by
  apply SSet.boundary.hom_ext (n := 1)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end boundary
end SSet
