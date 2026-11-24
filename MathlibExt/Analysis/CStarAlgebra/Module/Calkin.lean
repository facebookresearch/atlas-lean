/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary

/-!
# Calkin algebra of a right C-star module

For a complete right Hilbert `B`-module `E`, the module Calkin algebra is the
quotient of the adjointable endomorphism C-star algebra by its genuine closed
two-sided ideal of module-compact endomorphisms.

This file is a thin named interface over the existing closed-star-ideal
quotient. It supplies the explicit unital C-star dictionary, canonical class
map, zero/compact characteristic, and descent of unitary conjugation. It does
not identify module compactness with Banach-space compactness and assumes no
countable generation, fullness, separability, or sigma-unitality.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped CStarAlgebra RightActions

namespace CStarModule
namespace AdjointableOperator

universe uB uE uF uG

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable {F : Type uF}
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
variable {G : Type uG}
variable [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]

/-- The Calkin carrier of a complete right C-star module: adjointable
endomorphisms modulo the closed ideal of module-compact endomorphisms. -/
abbrev Calkin (B : Type uB) (E : Type uE)
    [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    [StarOrderedRing Bᵐᵒᵖ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] :=
  (compactClosedStarIdeal (B := B) (E := E)).Quotient

namespace Calkin

/-- The explicit unital C-star structure on the module Calkin carrier. It is
not installed as a global instance. -/
@[instance_reducible]
noncomputable def cStarAlgebra :
    CStarAlgebra (Calkin B E) :=
  (compactClosedStarIdeal (B := B) (E := E)).unitalQuotientCStarAlgebra

/-- The canonical unital star-algebra class map from adjointable
endomorphisms to the module Calkin algebra. -/
noncomputable def classStarAlgHom :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    End B E →⋆ₐ[ℂ] Calkin B E := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  exact I.unitalQuotientMap

/-- The class map is definitionally the existing closed-ideal quotient map. -/
theorem classStarAlgHom_apply (T : End B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    classStarAlgHom (B := B) (E := E) T =
      (compactClosedStarIdeal (B := B) (E := E)).quotientMap T := by
  rfl

/-- Every module-Calkin class has an adjointable representative. -/
theorem classStarAlgHom_surjective :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    Function.Surjective (classStarAlgHom (B := B) (E := E)) := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  change Function.Surjective I.unitalQuotientMap
  exact I.unitalQuotientMap_surjective

/-- An adjointable endomorphism has zero Calkin class exactly when it is
module-compact. This is module compactness, not Banach compactness. -/
@[simp]
theorem classStarAlgHom_eq_zero_iff (T : End B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    classStarAlgHom (B := B) (E := E) T = 0 ↔
      T ∈ compactSubmodule (B := B) (E := E) (F := E) := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  change I.unitalQuotientMap T = 0 ↔
    T ∈ compactSubmodule (B := B) (E := E) (F := E)
  constructor
  · intro h
    have hI : T ∈ I := (I.unitalQuotientMap_eq_zero_iff T).mp h
    change T ∈ compactSubmodule (B := B) (E := E) (F := E) at hI
    exact hI
  · intro h
    apply (I.unitalQuotientMap_eq_zero_iff T).mpr
    change T ∈ compactSubmodule (B := B) (E := E) (F := E)
    exact h

/-- Two adjointable endomorphisms define the same Calkin class exactly when
their difference is module-compact. -/
@[simp]
theorem classStarAlgHom_eq_iff (S T : End B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    classStarAlgHom (B := B) (E := E) S =
        classStarAlgHom (B := B) (E := E) T ↔
      S - T ∈ compactSubmodule (B := B) (E := E) (F := E) := by
  let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
  constructor
  · intro h
    apply (classStarAlgHom_eq_zero_iff (B := B) (E := E) (S - T)).mp
    rw [map_sub, h, sub_self]
  · intro h
    have hz :=
      (classStarAlgHom_eq_zero_iff (B := B) (E := E) (S - T)).mpr h
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz

omit [StarOrderedRing Bᵐᵒᵖ] [CompleteSpace E] [CompleteSpace F] in
/-- Conjugation by a Hilbert-module unitary sends module-compact
endomorphisms to module-compact endomorphisms. -/
theorem conjStarAlgHom_mem_compact
    (U : CStarModule.UnitaryEquiv B E F) {T : End B E}
    (hT : T ∈ compactSubmodule (B := B) (E := E) (F := E)) :
    U.conjStarAlgHom T ∈ compactSubmodule (B := B) (E := F) (F := F) := by
  have hfactor : U.conjStarAlgHom T =
      U.toAdjointable.comp
        (T.comp U.toAdjointable.adjointOperator) := by
    apply AdjointableOperator.ext
    intro y
    simp only [U.conjStarAlgHom_apply,
      AdjointableOperator.comp_apply, U.symm_apply,
      U.coe_toAdjointable]
  rw [hfactor]
  exact comp_mem_compact_right U.toAdjointable
    (comp_mem_compact_left hT U.toAdjointable.adjointOperator)

/-- Unitary conjugation maps the compact closed ideal into the target compact
closed ideal. -/
theorem conjStarAlgHom_mapsTo_compactClosedStarIdeal
    (U : CStarModule.UnitaryEquiv B E F) :
    Set.MapsTo U.conjStarAlgHom
      (compactClosedStarIdeal (B := B) (E := E))
      (compactClosedStarIdeal (B := B) (E := F)) := by
  intro T hT
  change T ∈ compactSubmodule (B := B) (E := E) (F := E) at hT
  change U.conjStarAlgHom T ∈
    compactSubmodule (B := B) (E := F) (F := F)
  exact conjStarAlgHom_mem_compact U hT

/-- The map of module Calkin algebras induced by unitary conjugation. -/
noncomputable def mapUnitary (U : CStarModule.UnitaryEquiv B E F) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
    Calkin B E →⋆ₙₐ[ℂ] Calkin B F := by
  let IE := compactClosedStarIdeal (B := B) (E := E)
  let IF := compactClosedStarIdeal (B := B) (E := F)
  let _ : IE.carrier.IsTwoSided := IE.isTwoSided
  let _ : IF.carrier.IsTwoSided := IF.isTwoSided
  let _ : CStarAlgebra IE.Quotient := IE.unitalQuotientCStarAlgebra
  let _ : CStarAlgebra IF.Quotient := IF.unitalQuotientCStarAlgebra
  let hmap : Set.MapsTo U.conjStarAlgHom.toNonUnitalStarAlgHom
      IE.carrier IF.carrier := by
    intro T hT
    change T ∈ compactSubmodule (B := B) (E := E) (F := E) at hT
    change U.conjStarAlgHom T ∈
      compactSubmodule (B := B) (E := F) (F := F)
    exact conjStarAlgHom_mem_compact U hT
  exact NonUnitalStarSubalgebra.Quotient.map IE.carrier IF.carrier
    U.conjStarAlgHom.toNonUnitalStarAlgHom hmap

/-- Unitary conjugation on Calkin algebras intertwines the two canonical class
maps. -/
@[simp]
theorem mapUnitary_classStarAlgHom_apply
    (U : CStarModule.UnitaryEquiv B E F) (T : End B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
    mapUnitary U (classStarAlgHom (B := B) (E := E) T) =
      classStarAlgHom (B := B) (E := F) (U.conjStarAlgHom T) := by
  let IE := compactClosedStarIdeal (B := B) (E := E)
  let IF := compactClosedStarIdeal (B := B) (E := F)
  let _ : IE.carrier.IsTwoSided := IE.isTwoSided
  let _ : IF.carrier.IsTwoSided := IF.isTwoSided
  let _ : CStarAlgebra IE.Quotient := IE.unitalQuotientCStarAlgebra
  let _ : CStarAlgebra IF.Quotient := IF.unitalQuotientCStarAlgebra
  let hmap : Set.MapsTo U.conjStarAlgHom.toNonUnitalStarAlgHom
      IE.carrier IF.carrier := by
    intro S hS
    change S ∈ compactSubmodule (B := B) (E := E) (F := E) at hS
    change U.conjStarAlgHom S ∈
      compactSubmodule (B := B) (E := F) (F := F)
    exact conjStarAlgHom_mem_compact U hS
  change NonUnitalStarSubalgebra.Quotient.map IE.carrier IF.carrier
      U.conjStarAlgHom.toNonUnitalStarAlgHom hmap (IE.quotientMap T) =
    IF.quotientMap (U.conjStarAlgHom T)
  exact NonUnitalStarSubalgebra.Quotient.map_mk IE.carrier IF.carrier
    U.conjStarAlgHom.toNonUnitalStarAlgHom hmap T

/-- Unitary conjugation induces a genuine star-algebra equivalence of module
Calkin algebras. -/
noncomputable def equivUnitary (U : CStarModule.UnitaryEquiv B E F) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
    Calkin B E ≃⋆ₐ[ℂ] Calkin B F := by
  let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
  let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
  let f := mapUnitary U
  let g := mapUnitary U.symm
  have hleft : Function.LeftInverse g f := by
    intro q
    obtain ⟨T, rfl⟩ :=
      (classStarAlgHom_surjective (B := B) (E := E)) q
    rw [mapUnitary_classStarAlgHom_apply,
      mapUnitary_classStarAlgHom_apply]
    congr 1
    have hsymm (x : E) : U.symm.symm x = U x := by
      change U.toAdjointable.adjointOperator.adjointOperator x = U x
      rw [AdjointableOperator.adjointOperator_adjointOperator]
      rfl
    apply AdjointableOperator.ext
    intro x
    simp only [CStarModule.UnitaryEquiv.conjStarAlgHom_apply,
      hsymm, U.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro q
    obtain ⟨T, rfl⟩ :=
      (classStarAlgHom_surjective (B := B) (E := F)) q
    rw [mapUnitary_classStarAlgHom_apply,
      mapUnitary_classStarAlgHom_apply]
    congr 1
    have hsymm (x : E) : U.symm.symm x = U x := by
      change U.toAdjointable.adjointOperator.adjointOperator x = U x
      rw [AdjointableOperator.adjointOperator_adjointOperator]
      rfl
    apply AdjointableOperator.ext
    intro y
    simp only [CStarModule.UnitaryEquiv.conjStarAlgHom_apply,
      hsymm, U.apply_symm_apply]
  exact StarAlgEquiv.ofBijective f ⟨hleft.injective, hright.surjective⟩

/-- The unitary-induced equivalence acts on represented classes by
conjugating their representatives. -/
@[simp]
theorem equivUnitary_classStarAlgHom_apply
    (U : CStarModule.UnitaryEquiv B E F) (T : End B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
    equivUnitary U (classStarAlgHom (B := B) (E := E) T) =
      classStarAlgHom (B := B) (E := F) (U.conjStarAlgHom T) := by
  exact mapUnitary_classStarAlgHom_apply U T

/-- The inverse of unitary transport is transport by the inverse module
unitary, on every Calkin class. -/
@[simp]
theorem equivUnitary_symm_apply
    (U : CStarModule.UnitaryEquiv B E F) (q : Calkin B F) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
    (equivUnitary U).symm q = equivUnitary U.symm q := by
  let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
  let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
  apply (equivUnitary U).symm_apply_eq.mpr
  obtain ⟨T, rfl⟩ :=
    (classStarAlgHom_surjective (B := B) (E := F)) q
  rw [equivUnitary_classStarAlgHom_apply, equivUnitary_classStarAlgHom_apply]
  congr 1
  apply AdjointableOperator.ext
  intro y
  have hsymm (x : E) : U.symm.symm x = U x := by
    change U.toAdjointable.adjointOperator.adjointOperator x = U x
    rw [AdjointableOperator.adjointOperator_adjointOperator]
    rfl
  simp only [CStarModule.UnitaryEquiv.conjStarAlgHom_apply,
    hsymm, U.apply_symm_apply]

/-- The identity unitary induces the identity map on module Calkin classes. -/
@[simp]
theorem equivUnitary_refl_apply (q : Calkin B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    equivUnitary (CStarModule.UnitaryEquiv.refl (B := B) (E := E)) q = q := by
  let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
  obtain ⟨T, rfl⟩ :=
    (classStarAlgHom_surjective (B := B) (E := E)) q
  rw [equivUnitary_classStarAlgHom_apply]
  congr 1
  apply AdjointableOperator.ext
  intro x
  rw [CStarModule.UnitaryEquiv.conjStarAlgHom_apply]
  rfl

/-- Composition of unitary module equivalences induces composition on module
Calkin classes. -/
theorem equivUnitary_trans_apply
    (U : CStarModule.UnitaryEquiv B E F)
    (V : CStarModule.UnitaryEquiv B F G) (q : Calkin B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
    let _ : CStarAlgebra (Calkin B G) := cStarAlgebra (B := B) (E := G)
    equivUnitary (U.trans V) q = equivUnitary V (equivUnitary U q) := by
  let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
  let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
  let _ : CStarAlgebra (Calkin B G) := cStarAlgebra (B := B) (E := G)
  obtain ⟨T, rfl⟩ :=
    (classStarAlgHom_surjective (B := B) (E := E)) q
  rw [equivUnitary_classStarAlgHom_apply,
    equivUnitary_classStarAlgHom_apply,
    equivUnitary_classStarAlgHom_apply]
  congr 1
  apply AdjointableOperator.ext
  intro z
  rw [CStarModule.UnitaryEquiv.conjStarAlgHom_apply,
    CStarModule.UnitaryEquiv.conjStarAlgHom_apply,
    CStarModule.UnitaryEquiv.conjStarAlgHom_apply,
    CStarModule.UnitaryEquiv.trans_apply]
  rfl

end Calkin
end AdjointableOperator
end CStarModule
