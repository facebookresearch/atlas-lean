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
# Calkin algebras of right C-star modules

For a complete right module `E` over a nonunital C-star algebra `B` with star-compatible
coefficient order, its Calkin algebra is `End_B(E) / K_B(E)`. Here `K_B(E)` is the norm-closed
span of the module rank-one maps `z ↦ x <• ⟨y,z⟩_B`. The quotient has its quotient C-star norm
and the identity class of the adjointable endomorphism algebra.

The quotient map sends `T` to `[T]`; `[T] = 0` exactly when `T ∈ K_B(E)`. A unitary `U : E ≃ F`
transports quotient classes by `[T] ↦ [U T U*]`, giving a star-algebra equivalence of the two
Calkin algebras. Inverse, identity and composition laws hold on all classes.
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

/-- **Calkin algebra of a Hilbert module.** For a complete right C-star module `E` over nonunital
`B`, this is `End_B(E) / K_B(E)`, the quotient by the closed ideal of module-compact
endomorphisms. -/
abbrev Calkin (B : Type uB) (E : Type uE)
    [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    [StarOrderedRing Bᵐᵒᵖ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] :=
  (compactClosedStarIdeal (B := B) (E := E)).Quotient

namespace Calkin

/-- **C-star structure on the module Calkin algebra.** The quotient `End_B(E) / K_B(E)` carries
its unital C-star algebra structure with the quotient norm. -/
@[instance_reducible]
noncomputable def cStarAlgebra :
    CStarAlgebra (Calkin B E) :=
  (compactClosedStarIdeal (B := B) (E := E)).unitalQuotientCStarAlgebra

/-- **Calkin quotient homomorphism.** For a complete right module, the unital star-algebra map
`End_B(E) → Calkin B E` sends `T` to its compact-ideal class `[T]`. -/
noncomputable def classStarAlgHom :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    End B E →⋆ₐ[ℂ] Calkin B E := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  exact I.unitalQuotientMap

/-- **Formula for the Calkin class map.** `classStarAlgHom T = compactClosedStarIdeal.quotientMap
T`, the quotient class of the adjointable endomorphism `T`. -/
theorem classStarAlgHom_apply (T : End B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    classStarAlgHom (B := B) (E := E) T =
      (compactClosedStarIdeal (B := B) (E := E)).quotientMap T := by
  rfl

/-- **Adjointable representatives of Calkin classes.** Every class in `Calkin B E` has a
representative `T : End_B(E)` under the compact-ideal quotient map. -/
theorem classStarAlgHom_surjective :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    Function.Surjective (classStarAlgHom (B := B) (E := E)) := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  change Function.Surjective I.unitalQuotientMap
  exact I.unitalQuotientMap_surjective

/-- **Zero Calkin class and module compactness.** For `T : End_B(E)`, `classStarAlgHom T = 0` if
and only if `T` lies in the module compact submodule `K_B(E)`. -/
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

/-- **Equality of Calkin classes.** Adjointable endomorphisms `S,T` define the same class if and
only if `S - T ∈ K_B(E)`. -/
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
/-- **Unitary invariance of module compactness.** For a unitary `U : E ≃ F`, `T ∈ K_B(E)` implies
`U T U* ∈ K_B(F)`. -/
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

/-- **Transport of the compact ideal.** Unitary conjugation `T ↦ U T U*` maps the compact closed
star ideal of `E` into that of `F`. -/
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

/-- **Unitary transport of Calkin classes.** A unitary `U : E ≃ F` induces the star-algebra map
`Calkin B E → Calkin B F` given by `[T] ↦ [U T U*]`. -/
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

/-- **Unitary transport and quotient representatives.** `mapUnitary U (classStarAlgHom T) =
classStarAlgHom (U.conjStarAlgHom T)`, so the image of `[T]` is `[U T U*]`. -/
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

/-- **Unitary equivalence of Calkin algebras.** A unitary `U : E ≃ F` gives a star-algebra
equivalence of the compact-ideal quotients, acting as `[T] ↦ [U T U*]`. -/
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

/-- **Action of the unitary-induced Calkin equivalence.** `equivUnitary U (classStarAlgHom T) =
classStarAlgHom (U.conjStarAlgHom T)` for each adjointable `T`. -/
@[simp]
theorem equivUnitary_classStarAlgHom_apply
    (U : CStarModule.UnitaryEquiv B E F) (T : End B E) :
    let _ : CStarAlgebra (Calkin B E) := cStarAlgebra (B := B) (E := E)
    let _ : CStarAlgebra (Calkin B F) := cStarAlgebra (B := B) (E := F)
    equivUnitary U (classStarAlgHom (B := B) (E := E) T) =
      classStarAlgHom (B := B) (E := F) (U.conjStarAlgHom T) := by
  exact mapUnitary_classStarAlgHom_apply U T

/-- **Inverse unitary transport on Calkin algebras.** `(equivUnitary U).symm q = equivUnitary
U.symm q` for every class `q : Calkin B F`. -/
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

/-- **Identity unitary on Calkin classes.** The equivalence induced by the identity unitary fixes
every class: `equivUnitary (UnitaryEquiv.refl) q = q`. -/
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

/-- **Composition of Calkin unitary transport.** For `U : E ≃ F` and `V : F ≃ G`, `equivUnitary
(U.trans V) q = equivUnitary V (equivUnitary U q)`. -/
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
