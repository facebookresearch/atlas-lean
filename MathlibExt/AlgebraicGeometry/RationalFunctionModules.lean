/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The sheaf of rational functions on an irreducible scheme

The sheaf `𝒦_X` of rational functions is the pushforward of the structure sheaf of
`Spec K(X)` along the canonical morphism `Spec K(X) ⟶ X`. Its sections over a nonempty open
subset are identified with the function field `K(X)`, compatibly with restriction.

This file is a port of part of `TauCeti/AlgebraicGeometry/Modules/RationalFunctions.lean` from
TauCetiProject/TauCeti at revision 62bbc0596dc3539d488232e4e924a338548ea0a9 (Apache 2.0):
every declaration here is copied from it with its proof; the namespace is changed, the rest of
the source API is omitted, and `functionFieldSectionsIso` is public.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RationalFunctionModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open _root_.AlgebraicGeometry _root_.Opposite

universe u

variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- The canonical morphism `Spec K(X) ⟶ X` from the spectrum of the function field of an
irreducible scheme, that is, the morphism from the spectrum of the stalk at the generic point. -/
def fromSpecFunctionField : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

variable {X}

/-- The generic point of an irreducible scheme lies in every nonempty open subset. -/
theorem genericPoint_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- A function on a nonempty open subset `U` acts on the function field through its germ at any
point of `U`. -/
theorem germ_smul_functionField {U : X.Opens} [Nonempty U] {x : X} (hx : x ∈ U) (r : Γ(X, U))
    (f : X.functionField) : X.presheaf.germ U x hx r • f = r • f := by
  rw [Algebra.smul_def, Algebra.smul_def, Scheme.algebraMap_germ_eq_germToFunctionField,
    RingHom.algebraMap_toAlgebra]

instance instUniqueSpecFunctionField (X : Scheme.{u}) [IrreducibleSpace X] :
    Unique (Spec X.functionField) where
  default := IsLocalRing.closedPoint X.functionField
  uniq p := by
    -- The morphism `Spec 𝒪_{X, x} ⟶ X` is a preimmersion, hence injective on points, and its
    -- range consists of the points specializing to `x`. Only the generic point of an irreducible
    -- space specializes to the generic point, so the source has a single point.
    refine (X.fromSpecStalk (genericPoint X)).isEmbedding.injective ?_
    refine Eq.trans ?_ Scheme.fromSpecStalk_closedPoint.symm
    have hmem : X.fromSpecStalk (genericPoint X) p ∈
        Set.range (X.fromSpecStalk (genericPoint X)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    have hclosure : closure ({genericPoint X} : Set X) ⊆
        closure ({X.fromSpecStalk (genericPoint X) p} : Set X) :=
      specializes_iff_closure_subset.mp hmem
    rw [genericPoint_closure] at hclosure
    exact ((genericPoint_spec X).eq (Set.univ_subset_iff.mp hclosure)).symm

/-- The sheaf of commutative rings underlying the rational-function sheaf: the pushforward of
the structure sheaf of `Spec K(X)` along `fromSpecFunctionField`. -/
def rationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    TopCat.Sheaf CommRingCat X :=
  (TopCat.Sheaf.pushforward CommRingCat (fromSpecFunctionField X).base).obj
    (Spec X.functionField).sheaf

/-- The canonical morphism of sheaves of rings `𝒪_X ⟶ 𝒦_X`. -/
def toRationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    X.sheaf ⟶ rationalFunctionsRing X where
  hom := (fromSpecFunctionField X).c

/-- The sheaf `𝒦_X` of rational functions on an integral scheme `X`: the constant sheaf with
value the function field, realized as the pushforward of the structure sheaf of `Spec K(X)`
along `fromSpecFunctionField`. -/
def rationalFunctions (X : Scheme.{u}) [IrreducibleSpace X] : X.Modules :=
  (Scheme.Modules.pushforward (fromSpecFunctionField X)).obj (SheafOfModules.unit _)

/-- For an open $U$ of the irreducible scheme $X$, the additive identification of the sections over
$U$ of the module sheaf $\mathcal{K}_X$ (`rationalFunctions`) with those of the ring sheaf
`rationalFunctionsRing`: both are the sections over $U$ of the pushforward of the structure sheaf
of $\operatorname{Spec} K(X)$ along $\operatorname{Spec} K(X) \to X$, and the identification is
the identity. -/
def rationalFunctionsSectionsEquiv (X : Scheme.{u}) [IrreducibleSpace X] (U : X.Opens) :
    (Γ(rationalFunctions X, U) : Type u) ≃+
      ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) :=
  AddEquiv.refl _

/-- The identification between module-sheaf and ring-sheaf sections commutes with restriction
maps. -/
@[simp]
theorem rationalFunctionsSectionsEquiv_map {U V : X.Opens} (i : U ⟶ V)
    (s : Γ(rationalFunctions X, V)) :
    rationalFunctionsSectionsEquiv X U ((rationalFunctions X).presheaf.map i.op s) =
      (rationalFunctionsRing X).presheaf.map i.op (rationalFunctionsSectionsEquiv X V s) :=
  by
    unfold rationalFunctionsSectionsEquiv rationalFunctions rationalFunctionsRing
    rfl

/-- On a nonempty open subset, the morphism `Spec K(X) ⟶ X` acts on sections by the germ map to
the function field. -/
theorem fromSpecFunctionField_app (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
        (Spec X.functionField).presheaf.map (homOfLE le_top).op :=
  Scheme.fromSpecStalk_app (genericPoint_mem U)

/-- The morphism `Spec K(X) ⟶ X` pulls every nonempty open subset back to the whole of
`Spec K(X)`, its source having a single point, which maps to the generic point. -/
@[simp]
theorem fromSpecFunctionField_preimage (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X) ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro p _
  apply TopologicalSpace.Opens.mem_map.mpr
  rw [Subsingleton.elim p (IsLocalRing.closedPoint X.functionField),
    fromSpecFunctionField, Scheme.fromSpecStalk_closedPoint]
  exact genericPoint_mem U

def functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U) ≅ X.functionField :=
  ((Spec X.functionField).presheaf.mapIso
    (eqToIso (fromSpecFunctionField_preimage U)).op).symm ≪≫ Scheme.ΓSpecIso X.functionField

/-- The sections of the ring sheaf `𝒦_X` over a nonempty open subset are the function field,
as commutative rings. -/
def rationalFunctionsRingEquiv (U : X.Opens) [Nonempty U] :
    ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) ≃+* X.functionField :=
  (functionFieldSectionsIso U).commRingCatIsoToRingEquiv

private theorem app_comp_functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U ≫ (functionFieldSectionsIso U).hom =
      X.germToFunctionField U := by
  rw [fromSpecFunctionField_app, functionFieldSectionsIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc,
    Subsingleton.elim ((homOfLE le_top).op ≫
      (eqToIso (fromSpecFunctionField_preimage U)).op.inv) (𝟙 _)]
  simp

private theorem map_comp_functionFieldSectionsIso {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) :
    (Spec X.functionField).presheaf.map
        ((Opens.map (fromSpecFunctionField X).base).map i).op ≫
      (functionFieldSectionsIso U).hom = (functionFieldSectionsIso V).hom := by
  rw [functionFieldSectionsIso, functionFieldSectionsIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Functor.map_comp_assoc,
    Subsingleton.elim (((Opens.map (fromSpecFunctionField X).base).map i).op ≫
      (eqToIso (fromSpecFunctionField_preimage U)).op.inv)
      (eqToIso (fromSpecFunctionField_preimage V)).op.inv]

/-- The ring equivalences identifying sections of `𝒦_X` with the function field commute with
restriction maps. -/
@[simp]
theorem rationalFunctionsRingEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : (rationalFunctionsRing X).presheaf.obj (.op V)) :
    rationalFunctionsRingEquiv U ((rationalFunctionsRing X).presheaf.map i.op s) =
      rationalFunctionsRingEquiv V s := by
  unfold rationalFunctionsRing at s ⊢
  -- The presheaf of a pushforward evaluates on `U` as the source presheaf evaluates on its
  -- preimage. This normalization exposes that documented pushforward computation so that
  -- `map_comp_functionFieldSectionsIso` applies.
  change (functionFieldSectionsIso U).hom
    ((Spec X.functionField).presheaf.map
      ((Opens.map (fromSpecFunctionField X).base).map i).op
        (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ V))) =
          (functionFieldSectionsIso V).hom s
  rw [← CategoryTheory.ConcreteCategory.comp_apply, map_comp_functionFieldSectionsIso]
  rfl

/-- The sections of `𝒦_X` over a nonempty open subset `U` are the function field, as a module
over the functions on `U`. -/
def rationalFunctionsEquiv (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X, U) ≃ₗ[Γ(X, U)] X.functionField :=
  { rationalFunctionsRingEquiv U with
    map_smul' r s := by
      -- The action of `Γ(X, U)` on the pushforward is multiplication after applying the map on
      -- sections, so multiplicativity of the identification reduces this to
      -- `app_comp_functionFieldSectionsIso`.
      -- The module-sheaf section type is definitionally the carrier of the corresponding
      -- pushforward ring section, which is the form used by that comparison lemma.
      change (functionFieldSectionsIso U).hom (r • s) =
        r • (functionFieldSectionsIso U).hom s
      have h : (functionFieldSectionsIso U).hom (r • s) =
          (functionFieldSectionsIso U).hom ((fromSpecFunctionField X).app U r *
            (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U))) := rfl
      rw [h, map_mul, ← CategoryTheory.ConcreteCategory.comp_apply,
        app_comp_functionFieldSectionsIso, Algebra.smul_def]
      rfl
  }

/-- The module-sheaf identification with the function field is the ring-sheaf identification
transported across `rationalFunctionsSectionsEquiv`. -/
theorem rationalFunctionsEquiv_apply (U : X.Opens) [Nonempty U]
    (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsEquiv U s =
      rationalFunctionsRingEquiv U (rationalFunctionsSectionsEquiv X U s) :=
  by
    unfold rationalFunctionsEquiv rationalFunctionsSectionsEquiv
    rfl

/-- The identifications of the sections of `𝒦_X` with the function field are compatible with the
restriction maps: `𝒦_X` is the constant sheaf. -/
@[simp]
theorem rationalFunctionsEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : Γ(rationalFunctions X, V)) :
    rationalFunctionsEquiv U ((rationalFunctions X).presheaf.map i.op s) =
      rationalFunctionsEquiv V s := by
  rw [rationalFunctionsEquiv_apply, rationalFunctionsSectionsEquiv_map,
    rationalFunctionsRingEquiv_map, rationalFunctionsEquiv_apply]


end MathlibExt.AlgebraicGeometry.RationalFunctionModules
