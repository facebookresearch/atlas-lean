/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MonoFunctorialFactorization

/-!
# Genuine small generators for the native marked mono weak factorization system

Minimally marked original boundary inclusions detect the underlying
simplicial mono right class. One original interval marking cell detects
marking reflection. Their actual countable family therefore has exactly
the right class of all marked monomorphisms, and its left lifting class
is precisely those monomorphisms by the proved native functorial weak
factorization system. This is genuine small generation for that system;
it does not assert the Cartesian marked weak-equivalence or model axioms.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- The original simplicial boundary inclusion with both native minimal markings. -/
def boundaryCell (n : ℕ) : min (∂Δ[n] : SSet.{u}) ⟶ min (Δ[n] : SSet.{u}) :=
  minimal.map (boundary.{u} n).ι

/-- The genuine countable boundary-and-marking generator index. -/
abbrev MonoCellIndex := ℕ ⊕ Unit

/-- The actual original boundary or one-edge marking cell. -/
def monoCell (s : MonoCellIndex) : Arrow Marked.{u} :=
  match s with
  | Sum.inl n => Arrow.mk (boundaryCell.{u} n)
  | Sum.inr _ => Arrow.mk edgeMarkCell.{u}

/-- The original countable native generator family for marked monomorphisms. -/
def monoCells : MorphismProperty Marked.{u} :=
  .ofHoms (fun s : MonoCellIndex => (monoCell.{u} s).hom)

/-- These actual native generators form a small family at the original value universe. -/
theorem monoCells_isSmall : IsSmall.{u} monoCells.{u} := by
  let _ : Small.{u} MonoCellIndex := small_zero _
  exact isSmall_ofHoms (fun s : MonoCellIndex => (monoCell.{u} s).hom)

/-- Lifting every original minimal boundary is exactly the underlying original simplicial mono right class. -/
theorem boundaryCell_rlp_iff {X Y : Marked.{u}} (p : X ⟶ Y) :
    (∀ n : ℕ, HasLiftingProperty (boundaryCell.{u} n) p) ↔
      (monomorphisms SSet.{u}).rlp p.hom := by
  rw [SSet.rlp_monomorphisms]
  constructor
  · intro hp A D i hi
    obtain ⟨n⟩ := hi
    exact (minimal_hasLiftingProperty_iff _ p).mp (hp n)
  · intro hp n
    apply (minimal_hasLiftingProperty_iff _ p).mpr
    exact hp _ (modelCategoryQuillen.boundary_ι_mem_I n)

/-- The small boundary-and-marking family has exactly the right class of all actual marked monomorphisms. -/
theorem monoCells_rlp_iff {X Y : Marked.{u}} (p : X ⟶ Y) :
    monoCells.{u}.rlp p ↔ (monomorphisms Marked.{u}).rlp p := by
  rw [monomorphisms_rlp_iff]
  constructor
  · intro hp
    have hb : ∀ n : ℕ, HasLiftingProperty (boundaryCell.{u} n) p :=
      fun n => hp _ (ofHoms.mk (f := fun s : MonoCellIndex => (monoCell.{u} s).hom) (.inl n))
    have hm : HasLiftingProperty edgeMarkCell.{u} p :=
      hp _ (ofHoms.mk (f := fun s : MonoCellIndex => (monoCell.{u} s).hom) (.inr ()))
    exact ⟨(boundaryCell_rlp_iff p).mp hb, (edgeMarkCell_rlp_iff p).mp hm⟩
  · rintro ⟨hb, hm⟩ A D i hi
    obtain ⟨s⟩ := hi
    rcases s with n | u
    · exact (boundaryCell_rlp_iff p).mpr hb n
    · exact (edgeMarkCell_rlp_iff p).mpr hm

/-- The complete actual right class is unchanged by replacing all marked monos with the countable native generators. -/
theorem monoCells_rlp_eq : monoCells.{u}.rlp = (monomorphisms Marked.{u}).rlp := by
  ext X Y p
  exact monoCells_rlp_iff p

/-- The actual countable native generators produce exactly all marked monomorphisms as their left lifting class. -/
theorem monoCells_generate_monomorphisms : monoCells.{u}.rlp.llp = monomorphisms Marked.{u} := by
  rw [monoCells_rlp_eq]
  exact mono_isWeakFactorizationSystem.llp

/-- The proved native factorization is also the genuine functorial factorization for these small generators. -/
theorem monoCells_hasFunctorialFactorization :
    HasFunctorialFactorization (monomorphisms Marked.{u}) monoCells.{u}.rlp := by
  rw [monoCells_rlp_eq]
  exact mono_hasFunctorialFactorization

end SSet.Marked
