/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoPermutationAction
public import MathlibExt.GroupTheory.PermutationBilinearMonomialExtension
public import MathlibExt.GroupTheory.GroupExtension.Pullback
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial

/-!
# The Milnor K₂ monomial central extension

Pulls the bilinear monomial extension back to determinant-one monomial matrices.
The resulting Milnor K₂ central extension has explicit inclusion and projection
maps and is natural under field homomorphisms.
-/

@[expose] public section

universe u v w

open Matrix
open PermutationBilinearCocycle
open MatsumotoPermutationAction
open GroupExtension

namespace MatsumotoMonomialExtension

/-- Determinant-one monomial subgroup, rank `n`. -/
abbrev M (F : Type u) [Field F] (n : ℕ) :=
  Matrix.GeneralLinearGroup.MonomialSL F (Fin n)

/-- Pullback total: determinant-one monomial lift in the Milnor K₂ monomial
central extension. -/
abbrev HM (F : Type u) [Field F] (n : ℕ) :=
  GroupExtension.PullbackTotal
    (PermutationBilinearCocycle.monomialGroupExtension
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n))
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

/-- Ambient monomial lift projection: first component of the pullback. -/
def ambientLiftHom (F : Type u) [Field F] (n : ℕ) :
    HM F n →* PermutationBilinearCocycle.MonomialLift
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n) :=
  GroupExtension.pullbackFst
    (PermutationBilinearCocycle.monomialGroupExtension
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n))
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

/-- Determinant-one base projection: second component of the pullback. -/
def projHom (F : Type u) [Field F] (n : ℕ) : HM F n →* M F n :=
  GroupExtension.pullbackSnd
    (PermutationBilinearCocycle.monomialGroupExtension
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n))
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

/-- Coefficient inclusion into the pullback total. -/
def inlHom (F : Type u) [Field F] (n : ℕ) :
    Multiplicative (MilnorK F 2) →* HM F n :=
  GroupExtension.pullbackInl
    (PermutationBilinearCocycle.monomialGroupExtension
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n))
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

@[simp]
theorem ambientLiftHom_coe (F : Type u) [Field F] (n : ℕ) (p : HM F n) :
    ambientLiftHom F n p =
      (p : PermutationBilinearCocycle.MonomialLift
        (milnorK2Bicharacter F) (Fin n) × M F n).1 := rfl

@[simp]
theorem projHom_coe (F : Type u) [Field F] (n : ℕ) (p : HM F n) :
    projHom F n p =
      (p : PermutationBilinearCocycle.MonomialLift
        (milnorK2Bicharacter F) (Fin n) × M F n).2 := rfl

@[simp]
theorem ambientLiftHom_mk (F : Type u) [Field F] (n : ℕ)
    {e} {h} {hp : (e, h) ∈
      (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter F) (Fin n)).pullbackSubgroup
        (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))} :
    ambientLiftHom F n (⟨(e, h), hp⟩ : HM F n) = e := rfl

@[simp]
theorem projHom_mk (F : Type u) [Field F] (n : ℕ)
    {e} {h} {hp} :
    projHom F n (⟨(e, h), hp⟩ : HM F n) = h := rfl

@[simp]
theorem pullback_condition (F : Type u) [Field F] (n : ℕ) (p : HM F n) :
    (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter F) (Fin n)).rightHom (ambientLiftHom F n p) =
      Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
        (projHom F n p) :=
  p.2

theorem pullback_square (F : Type u) [Field F] (n : ℕ) :
    (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter F) (Fin n)).rightHom.comp (ambientLiftHom F n) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)).comp
        (projHom F n) :=
  GroupExtension.pullback_square _ _

@[simp]
theorem ambientLiftHom_inl (F : Type u) [Field F] (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    ambientLiftHom F n (inlHom F n c) =
      (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter F) (Fin n)).inl c := rfl

@[simp]
theorem projHom_inl (F : Type u) [Field F] (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    projHom F n (inlHom F n c) = 1 := rfl

/-- Realization of determinant-one monomial matrices inside `SL`. -/
def toSL (F : Type u) [Field F] (n : ℕ) : M F n →* Matrix.SpecialLinearGroup (Fin n) F :=
  Matrix.GeneralLinearGroup.monomialSLHom F (Fin n)

@[simp]
theorem toSL_toGL (F : Type u) [Field F] (n : ℕ) (x : M F n) :
    (toSL F n x : Matrix.GeneralLinearGroup (Fin n) F) =
      Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin n)
        (x : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) :=
  Matrix.GeneralLinearGroup.monomialSLHom_toGL F (Fin n) x

@[simp]
theorem coe_toSL (F : Type u) [Field F] (n : ℕ) (x : M F n) :
    (↑(toSL F n x) : Matrix (Fin n) (Fin n) F) =
      (↑(Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin n)
        (x : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n))) :
        Matrix (Fin n) (Fin n) F) :=
  Matrix.GeneralLinearGroup.coe_monomialSLHom F (Fin n) x

/-- Central extension of determinant-one monomial matrices by `K₂`. -/
def monomialExtension (F : Type u) [Field F] (n : ℕ) :
    GroupExtension (Multiplicative (MilnorK F 2)) (HM F n) (M F n) :=
  GroupExtension.pullbackExtension
    (PermutationBilinearCocycle.monomialGroupExtension
      (milnorK2Bicharacter F) (Fin n))
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

theorem monomialExtension_isCentral (F : Type u) [Field F] (n : ℕ) :
    (monomialExtension F n).IsCentral :=
  GroupExtension.pullback_isCentral
    (PermutationBilinearCocycle.monomialGroupExtension
      (milnorK2Bicharacter F) (Fin n))
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
    (PermutationBilinearCocycle.monomialExtension_isCentral
      (ι := Fin n) (milnorK2Bicharacter F))

section Functoriality

variable {F : Type u} {K : Type v} {L : Type w} [Field F] [Field K] [Field L]

/-- Functoriality on determinant-one monomial matrices. -/
def MMap (f : F →+* K) (n : ℕ) : M F n →* M K n :=
  Matrix.GeneralLinearGroup.monomialSLMap F K (Fin n) f

/-- Ambient monomial lift functoriality via the generic `monomialLiftHom`. -/
noncomputable def ambientMonomialLiftMap (f : F →+* K) (n : ℕ) :
    PermutationBilinearCocycle.MonomialLift
        (milnorK2Bicharacter F) (Fin n) →*
      PermutationBilinearCocycle.MonomialLift
        (milnorK2Bicharacter K) (Fin n) :=
  PermutationBilinearCocycle.monomialLiftHom
    (MatsumotoPermutationAction.milnorK2BicharacterHom f)

/-- The field map on the ambient monomial group extensions. -/
noncomputable def ambientMonomialExtensionHom (f : F →+* K) (n : ℕ) :
    (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter F) (Fin n)).Hom
      (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter K) (Fin n)) where
  kernelHom := MilnorK.mapMultiplicative f 2
  totalHom := ambientMonomialLiftMap f n
  quotientHom :=
    PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
  inl_comm :=
    PermutationBilinearCocycle.monomialInl_naturality
      (MatsumotoPermutationAction.milnorK2BicharacterHom f)
  rightHom_comm :=
    PermutationBilinearCocycle.monomialProj_naturality
      (MatsumotoPermutationAction.milnorK2BicharacterHom f)

theorem coe_MMap (f : F →+* K) (n : ℕ) (x : M F n) :
    (↑(MMap (F := F) (K := K) f n x) :
        PermutationBilinearCocycle.MonomialBase Kˣ (Fin n)) =
      PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
        (x : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) :=
  Matrix.GeneralLinearGroup.coe_monomialSLMap F K (Fin n) f x

theorem monomialBaseHom_monomialSLToMonomialBase
    (f : F →+* K) (n : ℕ) (x : M F n) :
    PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
        ((Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)) x) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n))
        (MMap (F := F) (K := K) f n x) := by
  have h := coe_MMap (F := F) (K := K) f n x
  exact h.symm

/-- Compatibility of the determinant-one base map with the quotient component
of `ambientMonomialExtensionHom`. -/
theorem ambientMonomialExtensionHom_base_square (f : F →+* K) (n : ℕ) :
    (ambientMonomialExtensionHom (F := F) (K := K) f n).quotientHom.comp
        (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n)).comp
        (MMap (F := F) (K := K) f n) := by
  apply MonoidHom.ext
  intro x
  exact monomialBaseHom_monomialSLToMonomialBase
    (F := F) (K := K) f n x

theorem square_aux (f : F →+* K) (n : ℕ) (p : HM F n) :
    (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter K) (Fin n)).rightHom
        (ambientMonomialLiftMap (F := F) (K := K) f n (ambientLiftHom F n p)) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n))
        (MMap (F := F) (K := K) f n (projHom F n p)) := by
  have h_nat :
      (PermutationBilinearCocycle.monomialProjHom
          (MatsumotoPermutationAction.milnorK2Bicharacter K) (Fin n)).comp
          (ambientMonomialLiftMap (F := F) (K := K) f n) =
        (PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)).comp
          (PermutationBilinearCocycle.monomialProjHom
            (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)) :=
    PermutationBilinearCocycle.monomialProj_naturality
      (MatsumotoPermutationAction.milnorK2BicharacterHom f)
  have h1 :
      (PermutationBilinearCocycle.monomialProjHom
          (milnorK2Bicharacter K) (Fin n))
          (ambientMonomialLiftMap (F := F) (K := K) f n (ambientLiftHom F n p)) =
        PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
          ((PermutationBilinearCocycle.monomialProjHom
              (milnorK2Bicharacter F) (Fin n))
            (ambientLiftHom F n p)) := by
    calc (PermutationBilinearCocycle.monomialProjHom
            (milnorK2Bicharacter K) (Fin n))
            (ambientMonomialLiftMap (F := F) (K := K) f n (ambientLiftHom F n p))
        = ((PermutationBilinearCocycle.monomialProjHom
            (milnorK2Bicharacter K) (Fin n)).comp
            (ambientMonomialLiftMap (F := F) (K := K) f n)) (ambientLiftHom F n p) := rfl
      _ = ((PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)).comp
            (PermutationBilinearCocycle.monomialProjHom
              (milnorK2Bicharacter F) (Fin n))) (ambientLiftHom F n p) := by
          rw [h_nat]
      _ = _ := rfl
  have hpc :
      (PermutationBilinearCocycle.monomialProjHom
          (milnorK2Bicharacter F) (Fin n))
          (ambientLiftHom F n p) =
        (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
          (projHom F n p) :=
    pullback_condition F n p
  calc (PermutationBilinearCocycle.monomialGroupExtension
          (milnorK2Bicharacter K) (Fin n)).rightHom
          (ambientMonomialLiftMap (F := F) (K := K) f n (ambientLiftHom F n p))
      = (PermutationBilinearCocycle.monomialProjHom
          (milnorK2Bicharacter K) (Fin n))
          (ambientMonomialLiftMap (F := F) (K := K) f n (ambientLiftHom F n p)) := rfl
    _ = PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
          ((PermutationBilinearCocycle.monomialProjHom
              (milnorK2Bicharacter F) (Fin n))
            (ambientLiftHom F n p)) := h1
    _ = PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
          ((Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
            (projHom F n p)) := by
          rw [hpc]
    _ = (Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n))
          (MMap (F := F) (K := K) f n (projHom F n p)) := by
          rw [← monomialBaseHom_monomialSLToMonomialBase (F := F) (K := K) f n (projHom F n p)]

theorem square_eq (f : F →+* K) (n : ℕ) :
    (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter K) (Fin n)).rightHom.comp
        ((ambientMonomialLiftMap (F := F) (K := K) f n).comp (ambientLiftHom F n)) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n)).comp
        ((MMap (F := F) (K := K) f n).comp (projHom F n)) := by
  ext p : 1
  exact square_aux (F := F) (K := K) f n p

/-- The field map on determinant-one monomial extensions. -/
noncomputable def monomialExtensionHom (f : F →+* K) (n : ℕ) :
    (monomialExtension F n).Hom (monomialExtension K n) :=
  GroupExtension.pullbackExtensionHom
    (ambientMonomialExtensionHom (F := F) (K := K) f n)
    (MMap (F := F) (K := K) f n)
    (ambientMonomialExtensionHom_base_square (F := F) (K := K) f n)

/-- Determinant-one monomial lift, defined by functoriality of pullbacks. -/
noncomputable def HMMap (f : F →+* K) (n : ℕ) : HM F n →* HM K n :=
  GroupExtension.pullbackMap
    (ambientMonomialExtensionHom (F := F) (K := K) f n)
    (MMap (F := F) (K := K) f n)
    (ambientMonomialExtensionHom_base_square (F := F) (K := K) f n)

theorem HMMap_fst (f : F →+* K) (n : ℕ) (p : HM F n) :
    ambientLiftHom K n (HMMap (F := F) (K := K) f n p) =
      ambientMonomialLiftMap (F := F) (K := K) f n (ambientLiftHom F n p) := by
  exact GroupExtension.pullbackFst_pullbackMap
    (ambientMonomialExtensionHom (F := F) (K := K) f n)
    (MMap (F := F) (K := K) f n)
    (ambientMonomialExtensionHom_base_square (F := F) (K := K) f n) p

theorem HMMap_snd (f : F →+* K) (n : ℕ) (p : HM F n) :
    projHom K n (HMMap (F := F) (K := K) f n p) =
      MMap (F := F) (K := K) f n (projHom F n p) := by
  exact GroupExtension.pullbackSnd_pullbackMap
    (ambientMonomialExtensionHom (F := F) (K := K) f n)
    (MMap (F := F) (K := K) f n)
    (ambientMonomialExtensionHom_base_square (F := F) (K := K) f n) p

theorem ambientLiftHom_naturality (f : F →+* K) (n : ℕ) :
    (ambientLiftHom K n).comp (HMMap (F := F) (K := K) f n) =
      (ambientMonomialLiftMap (F := F) (K := K) f n).comp (ambientLiftHom F n) := by
  ext p : 1
  exact HMMap_fst (F := F) (K := K) f n p

theorem projHom_naturality (f : F →+* K) (n : ℕ) :
    (projHom K n).comp (HMMap (F := F) (K := K) f n) =
      (MMap (F := F) (K := K) f n).comp (projHom F n) := by
  ext p : 1
  exact HMMap_snd (F := F) (K := K) f n p

theorem inlHom_naturality (f : F →+* K) (n : ℕ) :
    (HMMap (F := F) (K := K) f n).comp (inlHom F n) =
      (inlHom K n).comp (MilnorK.mapMultiplicative f 2) :=
  (monomialExtensionHom (F := F) (K := K) f n).inl_comm

theorem MMap_id (n : ℕ) :
    MMap (F := F) (K := F) (RingHom.id F) n = MonoidHom.id (M F n) :=
  Matrix.GeneralLinearGroup.monomialSLMap_id F (Fin n)

theorem MMap_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    MMap (F := F) (K := L) (g.comp f) n =
      (MMap (F := K) (K := L) g n).comp (MMap (F := F) (K := K) f n) :=
  Matrix.GeneralLinearGroup.monomialSLMap_comp F K L (Fin n) f g

theorem ambientMonomialLiftMap_id (n : ℕ) :
    ambientMonomialLiftMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id
        (PermutationBilinearCocycle.MonomialLift
          (milnorK2Bicharacter F) (Fin n)) := by
  calc ambientMonomialLiftMap (F := F) (K := F) (RingHom.id F) n
      = PermutationBilinearCocycle.monomialLiftHom
          (milnorK2BicharacterHom (RingHom.id F)) := rfl
    _ = PermutationBilinearCocycle.monomialLiftHom
          (PermutationBilinearCocycle.SkewBicharacter.Hom.id
            (milnorK2Bicharacter F)) := by
          rw [milnorK2BicharacterHom_id]
    _ = MonoidHom.id _ :=
          PermutationBilinearCocycle.monomialLiftHom_id
            (milnorK2Bicharacter F)

theorem ambientMonomialLiftMap_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    ambientMonomialLiftMap (F := F) (K := L) (g.comp f) n =
      (ambientMonomialLiftMap (F := K) (K := L) g n).comp
        (ambientMonomialLiftMap (F := F) (K := K) f n) := by
  calc ambientMonomialLiftMap (F := F) (K := L) (g.comp f) n
      = PermutationBilinearCocycle.monomialLiftHom
          (milnorK2BicharacterHom (g.comp f)) := rfl
    _ = PermutationBilinearCocycle.monomialLiftHom
          (PermutationBilinearCocycle.SkewBicharacter.Hom.comp
            (milnorK2BicharacterHom f) (milnorK2BicharacterHom g)) := by
          rw [milnorK2BicharacterHom_comp]
    _ = (PermutationBilinearCocycle.monomialLiftHom
          (milnorK2BicharacterHom g)).comp
          (PermutationBilinearCocycle.monomialLiftHom
            (milnorK2BicharacterHom f)) :=
          PermutationBilinearCocycle.monomialLiftHom_comp
            (milnorK2BicharacterHom f) (milnorK2BicharacterHom g)
    _ = (ambientMonomialLiftMap (F := K) (K := L) g n).comp
          (ambientMonomialLiftMap (F := F) (K := K) f n) := rfl

theorem ambientMonomialExtensionHom_id (n : ℕ) :
    ambientMonomialExtensionHom (F := F) (K := F) (RingHom.id F) n =
      GroupExtension.Hom.id
        (PermutationBilinearCocycle.monomialGroupExtension
          (milnorK2Bicharacter F) (Fin n)) := by
  apply GroupExtension.Hom.ext
  exact ambientMonomialLiftMap_id (F := F) n

theorem ambientMonomialExtensionHom_comp
    (f : F →+* K) (g : K →+* L) (n : ℕ) :
    ambientMonomialExtensionHom (F := F) (K := L) (g.comp f) n =
      (ambientMonomialExtensionHom (F := K) (K := L) g n).comp
        (ambientMonomialExtensionHom (F := F) (K := K) f n) := by
  apply GroupExtension.Hom.ext
  exact ambientMonomialLiftMap_comp (F := F) (K := K) (L := L) f g n

theorem HMMap_id (n : ℕ) :
    HMMap (F := F) (K := F) (RingHom.id F) n = MonoidHom.id (HM F n) := by
  unfold HMMap
  simpa only [ambientMonomialExtensionHom_id, MMap_id] using
    GroupExtension.pullbackMap_id
      (PermutationBilinearCocycle.monomialGroupExtension
        (milnorK2Bicharacter F) (Fin n))
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

theorem HMMap_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    HMMap (F := F) (K := L) (g.comp f) n =
      (HMMap (F := K) (K := L) g n).comp (HMMap (F := F) (K := K) f n) := by
  unfold HMMap
  simpa only [ambientMonomialExtensionHom_comp, MMap_comp] using
    GroupExtension.pullbackMap_comp
      (ambientMonomialExtensionHom (F := F) (K := K) f n)
      (ambientMonomialExtensionHom (F := K) (K := L) g n)
      (MMap (F := F) (K := K) f n)
      (MMap (F := K) (K := L) g n)
      (ambientMonomialExtensionHom_base_square (F := F) (K := K) f n)
      (ambientMonomialExtensionHom_base_square (F := K) (K := L) g n)

end Functoriality

/-
Matrix realization naturality follows from the generic
`monomialMatrixHom_mapRingHom` / `monomialSLMap` API combined with
`SpecialLinearGroup.map`. We omit a bundled `toSL` naturality statement
here because Mathlib's `SpecialLinearGroup.map` API would require
additional coercion plumbing disproportionate to this thin facade.
-/

end MatsumotoMonomialExtension

end
