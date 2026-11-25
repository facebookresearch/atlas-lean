/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Flat
public import MathlibExt.Algebra.Homology.HomologicalComplex.CyclesImage
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Basic.UnivLE

/-!
# Tor boundaries for cycles and homology

The incoming-boundary, cycles and homology short exact sequence gives a map from
first Tor of homology to the boundary module tensored with an arbitrary left
coefficient. Its degree-zero comparison is the native left-derived comparison.

Exact tensor functors on the term and its outgoing image make the cycles module
flat. The Tor boundary then identifies first Tor with the kernel of the tensor
boundary inclusion. The complex shape and coefficient module are arbitrary.
Native lifts retain independent carrier worlds and any common lift height.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex.BalancedTensor

universe u v w t κ

variable (R : Type u) [Ring R]
variable {ι : Type κ} {c : ComplexShape ι}

section Resolutions

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]
variable (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{v} R)
  (i j : ι) (hi : c.prev j = i)

/-- The native Tor boundary, followed by the canonical degree-zero comparison. -/
def torBoundary :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology j)).obj N ⟶
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (Abelian.image (P.d i j))).obj N := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive (ModuleCat.BalancedTensor.groupBifunctor R) N
  let S := HomologicalComplex.boundariesCyclesHomologySequence P i j
  let hS : S.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P i j hi
  change (F.leftDerived 1).obj S.X₃ ⟶ F.obj S.X₁
  exact LeftDerivedDelta.LDdelta F 0 S hS ≫ (F.leftDerivedZeroIsoSelf.app S.X₁).hom

/-- The Tor boundary is killed by the actual tensor boundary inclusion. -/
@[reassoc]
theorem torBoundary_comp_boundaryTensor :
    torBoundary R P N i j hi ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).map
          (HomologicalComplex.boundaryCyclesMap P i j)).app N = 0 := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive (ModuleCat.BalancedTensor.groupBifunctor R) N
  let S := HomologicalComplex.boundariesCyclesHomologySequence P i j
  let hS : S.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P i j hi
  obtain ⟨hz, _⟩ := LeftDerivedDelta.LDexact_A F 0 S hS
  let e : F.leftDerived 0 ≅ F := F.leftDerivedZeroIsoSelf
  change (LeftDerivedDelta.LDdelta F 0 S hS ≫ (e.app S.X₁).hom) ≫ F.map S.f = 0
  rw [Category.assoc, ← e.hom.naturality S.f, ← Category.assoc, hz, zero_comp]

/-- The Tor boundary and the tensor inclusion form an exact short complex. -/
def torBoundaryTensorSequence : ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (torBoundary R P N i j hi)
    (((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap P i j)).app N)
    (torBoundary_comp_boundaryTensor R P N i j hi)

/-- The native degree-zero comparisons transport exactness to the tensor inclusion. -/
theorem torBoundaryTensorSequence_exact :
    (torBoundaryTensorSequence R P N i j hi).Exact := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive (ModuleCat.BalancedTensor.groupBifunctor R) N
  let S := HomologicalComplex.boundariesCyclesHomologySequence P i j
  let hS : S.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P i j hi
  obtain ⟨hz, hExact⟩ := LeftDerivedDelta.LDexact_A F 0 S hS
  let T := ShortComplex.mk (LeftDerivedDelta.LDdelta F 0 S hS) ((F.leftDerived 0).map S.f) hz
  let e : F.leftDerived 0 ≅ F := F.leftDerivedZeroIsoSelf
  let eT : T ≅ torBoundaryTensorSequence R P N i j hi :=
    ShortComplex.isoMk (Iso.refl _) (e.app S.X₁) (e.app S.X₂)
      (by
        change (𝟙 _) ≫ (LeftDerivedDelta.LDdelta F 0 S hS ≫ (e.app S.X₁).hom) = _
        exact Category.id_comp _)
      (by
        change (e.app S.X₁).hom ≫ F.map S.f =
          (F.leftDerived 0).map S.f ≫ (e.app S.X₂).hom
        exact (e.hom.naturality S.f).symm)
  exact ShortComplex.exact_of_iso eT hExact

/-- Every original complex map commutes with the Tor boundary and differential-image map. -/
theorem torBoundary_naturality
    {K L : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c} (φ : K ⟶ L) :
    ((ModuleCat.BalancedTensor.torFirst R 1).map (HomologicalComplex.homologyMap φ j)).app N ≫
        torBoundary R L N i j hi =
      torBoundary R K N i j hi ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).map
          (((HomologicalComplex.boundariesCyclesHomologySequenceFunctor
            (C := ModuleCat.{v} Rᵐᵒᵖ) (c := c) i j).map φ).τ₁)).app N := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive (ModuleCat.BalancedTensor.groupBifunctor R) N
  let SK := HomologicalComplex.boundariesCyclesHomologySequence K i j
  let SL := HomologicalComplex.boundariesCyclesHomologySequence L i j
  let hK : SK.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact K i j hi
  let hL : SL.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact L i j hi
  let ψ : SK ⟶ SL :=
    (HomologicalComplex.boundariesCyclesHomologySequenceFunctor
      (C := ModuleCat.{v} Rᵐᵒᵖ) (c := c) i j).map φ
  have h₃ : ψ.τ₃ = HomologicalComplex.homologyMap φ j :=
    HomologicalComplex.boundariesCyclesHomologySequenceFunctor_map_τ₃ φ i j
  let e : F.leftDerived 0 ≅ F := F.leftDerivedZeroIsoSelf
  have hδ := LeftDerivedDelta.LDdelta_natural F 0 SL SK ψ hL hK
  rw [← h₃]
  change (F.leftDerived 1).map ψ.τ₃ ≫
      (LeftDerivedDelta.LDdelta F 0 SL hL ≫ (e.app SL.X₁).hom) =
    (LeftDerivedDelta.LDdelta F 0 SK hK ≫ (e.app SK.X₁).hom) ≫ F.map ψ.τ₁
  calc
    _ = (LeftDerivedDelta.LDdelta F 0 SK hK ≫ (F.leftDerived 0).map ψ.τ₁) ≫
        (e.app SL.X₁).hom := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ (e.app SL.X₁).hom) hδ
    _ = _ := by
      simp only [Category.assoc]
      rw [e.hom.naturality ψ.τ₁]

section Flat

variable [((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X j)).PreservesHomology]
  [((ModuleCat.BalancedTensor.groupBifunctor R).obj
    (Abelian.image (P.d j (c.next j)))).PreservesHomology]

private theorem cyclesTorOneIsZero :
    IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (P.cycles j)).obj N) := by
  let S := HomologicalComplex.cyclesImageSequence P j (c.next j)
  have hS : S.ShortExact := HomologicalComplex.cyclesImageSequence_shortExact P j (c.next j) rfl
  exact ModuleCat.BalancedTensor.isZero_torFirst_one_of_shortExact R hS
    (fun B => (ModuleCat.BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
      R (P.X j)).1 (Functor.preservesFiniteLimits_of_preservesHomology
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X j))) B)
    (fun B => (ModuleCat.BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
      R (Abelian.image (P.d j (c.next j)))).1 (Functor.preservesFiniteLimits_of_preservesHomology
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj
          (Abelian.image (P.d j (c.next j))))) B) N

/-- Flatness earned on cycles makes the canonical Tor boundary injective. -/
theorem torBoundary_mono : Mono (torBoundary R P N i j hi) := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive (ModuleCat.BalancedTensor.groupBifunctor R) N
  let S := HomologicalComplex.boundariesCyclesHomologySequence P i j
  let hS : S.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P i j hi
  obtain ⟨hz, hExact⟩ := LeftDerivedDelta.LDexact_C F 0 S hS
  let T := ShortComplex.mk ((F.leftDerived 1).map S.g) (LeftDerivedDelta.LDdelta F 0 S hS) hz
  have hCycles : IsZero ((F.leftDerived 1).obj S.X₂) := by
    change IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (P.cycles j)).obj N)
    exact cyclesTorOneIsZero R P N j
  have hg : (F.leftDerived 1).map S.g = 0 := hCycles.eq_of_src _ 0
  let : Mono (LeftDerivedDelta.LDdelta F 0 S hS) := (T.exact_iff_mono hg).1 hExact
  change Mono (LeftDerivedDelta.LDdelta F 0 S hS ≫ (F.leftDerivedZeroIsoSelf.app S.X₁).hom)
  infer_instance

/-- First Tor of the actual homology module is the tensor boundary-inclusion kernel. -/
def torBoundaryKernelIso :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology j)).obj N ≅
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N) := by
  let k := kernel.lift
    (((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap P i j)).app N)
    (torBoundary R P N i j hi) (torBoundary_comp_boundaryTensor R P N i j hi)
  let : Mono (torBoundary R P N i j hi) := torBoundary_mono R P N i j hi
  let : Mono k := inferInstance
  let : Epi k := (torBoundaryTensorSequence_exact R P N i j hi).epi_kernelLift
  let : IsIso k := inferInstance
  exact asIso k

/-- The forward kernel comparison recovers the original positive Tor boundary. -/
@[reassoc]
theorem torBoundaryKernelIso_hom_ι :
    (torBoundaryKernelIso R P N i j hi).hom ≫
        kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
          (HomologicalComplex.boundaryCyclesMap P i j)).app N) =
      torBoundary R P N i j hi := by
  change kernel.lift
      (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N)
      (torBoundary R P N i j hi) (torBoundary_comp_boundaryTensor R P N i j hi) ≫
      kernel.ι _ = _
  exact kernel.lift_ι _ _ _

/-- The inverse comparison followed by the boundary is the native kernel inclusion. -/
@[reassoc]
theorem torBoundaryKernelIso_inv_boundary :
    (torBoundaryKernelIso R P N i j hi).inv ≫ torBoundary R P N i j hi =
      kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N) := by
  rw [← torBoundaryKernelIso_hom_ι R P N i j hi]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Flat
end Resolutions

/-- The same native Tor boundary after independent module lifts to a common world. -/
def torBoundaryAt
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{w} R)
    (i j : ι) (hi : c.prev j = i) :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj
      ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P).homology
        j)).obj ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N) ⟶
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj
        (Abelian.image
          ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P).d
            i j))).obj ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N) := by
  let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
  let NL : ModuleCat.{max u v w t} R := (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} R) := inferInstance
  exact torBoundary R PL NL i j hi

/-- The kernel comparison in the actual common world needs only its lifted term and image. -/
def torBoundaryKernelIsoAt
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{w} R)
    (i j : ι) (hi : c.prev j = i)
    [((ModuleCat.BalancedTensor.groupBifunctor R).obj
      ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P).X
        j)).PreservesHomology]
    [((ModuleCat.BalancedTensor.groupBifunctor R).obj
      (Abelian.image
        ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P).d
          j (c.next j)))).PreservesHomology] :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj
      ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P).homology
        j)).obj ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N) ≅
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap
          (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P)
          i j)).app ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N)) := by
  let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
  let NL : ModuleCat.{max u v w t} R := (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} R) := inferInstance
  exact torBoundaryKernelIso R PL NL i j hi

end HomologicalComplex.BalancedTensor
