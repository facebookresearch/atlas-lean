/-
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
Authors: @junekim623, Muse
Provenance: original construction for Hartshorne III.6 foundations on ringed
spaces: the local-to-global Ext edge morphism.
Author: @toskua
Promotion contribution: generic short-complex homology comparison API.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import MathlibExt.Algebra.Homology.Functor

/-!
# The canonical forward homology edge of a left-exact functor
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
variable (S : ShortComplex C) [S.HasHomology] [(S.map F).HasHomology]

/-- Actual cycles map to images of original cycles through the preserved
native kernel, without any cokernel-preservation assumption. -/
def leftExactCyclesComparison : (S.map F).cycles ⟶ F.obj S.cycles := by
  let c := KernelFork.ofι S.iCycles S.iCycles_g
  let h : IsLimit (c.map F) := KernelFork.mapIsLimit c S.cyclesIsKernel F
  exact h.lift (KernelFork.ofι (S.map F).iCycles (S.map F).iCycles_g)

theorem leftExactCyclesComparison_i :
    leftExactCyclesComparison F S ≫ F.map S.iCycles = (S.map F).iCycles := by
  let c := KernelFork.ofι S.iCycles S.iCycles_g
  let h : IsLimit (c.map F) := KernelFork.mapIsLimit c S.cyclesIsKernel F
  exact Fork.IsLimit.lift_ι
    (t := KernelFork.ofι (S.map F).iCycles (S.map F).iCycles_g) h

/-- Preservation of the genuine cycles kernel makes its comparison an isomorphism. -/
instance isIso_leftExactCyclesComparison : IsIso (leftExactCyclesComparison F S) := by
  let c := KernelFork.ofι S.iCycles S.iCycles_g
  let h : IsLimit (c.map F) := KernelFork.mapIsLimit c S.cyclesIsKernel F
  let e := (S.map F).isoCyclesOfIsLimit h
  let _ : Mono (F.map S.iCycles) := mono_of_isLimit_fork h
  have hComparison : leftExactCyclesComparison F S = e.inv := by
    apply (cancel_mono (F.map S.iCycles)).mp
    exact (leftExactCyclesComparison_i F S).trans ((S.map F).isoCyclesOfIsLimit_inv_ι h).symm
  rw [hComparison]
  infer_instance

/-- The cycles comparison isomorphism of a left-exact, zero-preserving functor. -/
def leftExactCyclesComparisonIso : (S.map F).cycles ≅ F.obj S.cycles :=
  asIso (leftExactCyclesComparison F S)

/-- The isomorphism retains the canonical comparison morphism. -/
theorem leftExactCyclesComparisonIso_hom :
    (leftExactCyclesComparisonIso F S).hom = leftExactCyclesComparison F S := rfl

theorem leftExactCyclesComparison_toCycles :
    (S.map F).toCycles ≫ leftExactCyclesComparison F S = F.map S.toCycles := by
  let c := KernelFork.ofι S.iCycles S.iCycles_g
  let h : IsLimit (c.map F) := KernelFork.mapIsLimit c S.cyclesIsKernel F
  let _ : Mono (F.map S.iCycles) := mono_of_isLimit_fork h
  apply (cancel_mono (F.map S.iCycles)).mp
  rw [Category.assoc, leftExactCyclesComparison_i, (S.map F).toCycles_i,
    ← F.map_comp, S.toCycles_i]
  rfl

theorem leftExactHomologyEdge_kills_boundaries :
    (S.map F).toCycles ≫ (leftExactCyclesComparison F S ≫ F.map S.homologyπ) = 0 := by
  rw [← Category.assoc, leftExactCyclesComparison_toCycles, ← F.map_comp,
    S.toCycles_comp_homologyπ, F.map_zero]

/-- The literal forward homology map induced by a genuinely left-exact
functor; no homology-preservation or comparison Iso is assumed. -/
def leftExactHomologyEdge : (S.map F).homology ⟶ F.obj S.homology :=
  (S.map F).descHomology (leftExactCyclesComparison F S ≫ F.map S.homologyπ)
    (leftExactHomologyEdge_kills_boundaries F S)

/-- Its original cycles/homology projection characteristic. -/
theorem leftExactHomologyEdge_characteristic :
    (S.map F).homologyπ ≫ leftExactHomologyEdge F S =
      leftExactCyclesComparison F S ≫ F.map S.homologyπ :=
  (S.map F).π_descHomology _ _

section ComplexMorphism

variable (T : ShortComplex C) [T.HasHomology] [(T.map F).HasHomology] (φ : S ⟶ T)

/-- The preserved-kernel cycles comparison is natural in short-complex morphisms. -/
theorem leftExactCyclesComparison_map_naturality :
    ShortComplex.cyclesMap (S₁ := S.map F) (S₂ := T.map F)
      (F.mapShortComplex.map φ) ≫ leftExactCyclesComparison F T =
      leftExactCyclesComparison F S ≫ F.map (ShortComplex.cyclesMap φ) := by
  let c := KernelFork.ofι T.iCycles T.iCycles_g
  let h : IsLimit (c.map F) := KernelFork.mapIsLimit c T.cyclesIsKernel F
  let _ : Mono (F.map T.iCycles) := mono_of_isLimit_fork h
  apply (cancel_mono (F.map T.iCycles)).mp
  calc
    _ = (S.map F).iCycles ≫ F.map φ.τ₂ := by
      rw [Category.assoc, leftExactCyclesComparison_i, ShortComplex.cyclesMap_i]
      rfl
    _ = (leftExactCyclesComparison F S ≫ F.map S.iCycles) ≫ F.map φ.τ₂ :=
      congrArg (· ≫ F.map φ.τ₂) (leftExactCyclesComparison_i F S).symm
    _ = leftExactCyclesComparison F S ≫ F.map (S.iCycles ≫ φ.τ₂) :=
      (Category.assoc _ _ _).trans
        (congrArg (leftExactCyclesComparison F S ≫ ·) (F.map_comp S.iCycles φ.τ₂).symm)
    _ = leftExactCyclesComparison F S ≫ F.map (ShortComplex.cyclesMap φ ≫ T.iCycles) :=
      congrArg (fun a => leftExactCyclesComparison F S ≫ F.map a)
        (ShortComplex.cyclesMap_i φ).symm
    _ = leftExactCyclesComparison F S ≫
        (F.map (ShortComplex.cyclesMap φ) ≫ F.map T.iCycles) :=
      congrArg (leftExactCyclesComparison F S ≫ ·) (F.map_comp _ _)
    _ = _ := (Category.assoc _ _ _).symm

/-- The forward homology edge is natural in short-complex morphisms without
assuming preservation of homology or cokernels. -/
theorem leftExactHomologyEdge_map_naturality :
    ShortComplex.homologyMap (S₁ := S.map F) (S₂ := T.map F)
      (F.mapShortComplex.map φ) ≫ leftExactHomologyEdge F T =
      leftExactHomologyEdge F S ≫ F.map (ShortComplex.homologyMap φ) := by
  let ψ : S.map F ⟶ T.map F := F.mapShortComplex.map φ
  apply (cancel_epi (S.map F).homologyπ).mp
  calc
    _ = ((S.map F).homologyπ ≫ ShortComplex.homologyMap ψ) ≫ leftExactHomologyEdge F T :=
      (Category.assoc _ _ _).symm
    _ = (ShortComplex.cyclesMap ψ ≫ (T.map F).homologyπ) ≫ leftExactHomologyEdge F T :=
      congrArg (· ≫ leftExactHomologyEdge F T) (ShortComplex.homologyπ_naturality ψ)
    _ = ShortComplex.cyclesMap ψ ≫
        (leftExactCyclesComparison F T ≫ F.map T.homologyπ) :=
      (Category.assoc _ _ _).trans
        (congrArg (ShortComplex.cyclesMap ψ ≫ ·) (leftExactHomologyEdge_characteristic F T))
    _ = (leftExactCyclesComparison F S ≫ F.map (ShortComplex.cyclesMap φ)) ≫ F.map T.homologyπ :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ F.map T.homologyπ) (leftExactCyclesComparison_map_naturality F S T φ))
    _ = leftExactCyclesComparison F S ≫ F.map (ShortComplex.cyclesMap φ ≫ T.homologyπ) :=
      (Category.assoc _ _ _).trans
        (congrArg (leftExactCyclesComparison F S ≫ ·) (F.map_comp _ _).symm)
    _ = leftExactCyclesComparison F S ≫ F.map (S.homologyπ ≫ ShortComplex.homologyMap φ) :=
      congrArg (fun a => leftExactCyclesComparison F S ≫ F.map a)
        (ShortComplex.homologyπ_naturality φ).symm
    _ = (leftExactCyclesComparison F S ≫ F.map S.homologyπ) ≫
        F.map (ShortComplex.homologyMap φ) :=
      (congrArg (leftExactCyclesComparison F S ≫ ·) (F.map_comp _ _)).trans
        (Category.assoc _ _ _).symm
    _ = ((S.map F).homologyπ ≫ leftExactHomologyEdge F S) ≫
        F.map (ShortComplex.homologyMap φ) :=
      congrArg (· ≫ F.map (ShortComplex.homologyMap φ)) (leftExactHomologyEdge_characteristic F S).symm
    _ = _ := Category.assoc _ _ _

end ComplexMorphism

section Naturality

variable (G : C ⥤ D) [G.PreservesZeroMorphisms] [PreservesFiniteLimits G]
variable [(S.map G).HasHomology] (τ : F ⟶ G)

/-- Actual cycles comparison is natural between genuinely left-exact functors. -/
theorem leftExactCyclesComparison_naturality :
    ShortComplex.cyclesMap (S.mapNatTrans τ) ≫ leftExactCyclesComparison G S =
      leftExactCyclesComparison F S ≫ τ.app S.cycles := by
  let φ : S.map F ⟶ S.map G := S.mapNatTrans τ
  let c := KernelFork.ofι S.iCycles S.iCycles_g
  let h : IsLimit (c.map G) := KernelFork.mapIsLimit c S.cyclesIsKernel G
  let _ : Mono (G.map S.iCycles) := mono_of_isLimit_fork h
  apply (cancel_mono (G.map S.iCycles)).mp
  change (ShortComplex.cyclesMap φ ≫ leftExactCyclesComparison G S) ≫ G.map S.iCycles =
    (leftExactCyclesComparison F S ≫ τ.app S.cycles) ≫ G.map S.iCycles
  calc
    _ = (S.map F).iCycles ≫ τ.app S.X₂ := by
      rw [Category.assoc, leftExactCyclesComparison_i, ShortComplex.cyclesMap_i]
      rfl
    _ = (leftExactCyclesComparison F S ≫ F.map S.iCycles) ≫ τ.app S.X₂ :=
      congrArg (fun a => a ≫ τ.app S.X₂) (leftExactCyclesComparison_i F S).symm
    _ = leftExactCyclesComparison F S ≫ (F.map S.iCycles ≫ τ.app S.X₂) :=
      Category.assoc _ _ _
    _ = leftExactCyclesComparison F S ≫ (τ.app S.cycles ≫ G.map S.iCycles) :=
      congrArg (fun a => leftExactCyclesComparison F S ≫ a) (τ.naturality S.iCycles)
    _ = _ := (Category.assoc _ _ _).symm

/-- The genuine forward homology edge is natural; no homology preservation
of the compact section functor is used. -/
theorem leftExactHomologyEdge_naturality :
    ShortComplex.homologyMap (S.mapNatTrans τ) ≫ leftExactHomologyEdge G S =
      leftExactHomologyEdge F S ≫ τ.app S.homology := by
  let φ : S.map F ⟶ S.map G := S.mapNatTrans τ
  apply (cancel_epi (S.map F).homologyπ).mp
  calc
    _ = ((S.map F).homologyπ ≫ ShortComplex.homologyMap φ) ≫
        leftExactHomologyEdge G S := (Category.assoc _ _ _).symm
    _ = (ShortComplex.cyclesMap φ ≫ (S.map G).homologyπ) ≫
        leftExactHomologyEdge G S :=
      congrArg (fun a => a ≫ leftExactHomologyEdge G S)
        (ShortComplex.homologyπ_naturality φ)
    _ = ShortComplex.cyclesMap φ ≫
        ((S.map G).homologyπ ≫ leftExactHomologyEdge G S) := Category.assoc _ _ _
    _ = ShortComplex.cyclesMap φ ≫
        (leftExactCyclesComparison G S ≫ G.map S.homologyπ) :=
      congrArg (fun a => ShortComplex.cyclesMap φ ≫ a)
        (leftExactHomologyEdge_characteristic G S)
    _ = (ShortComplex.cyclesMap φ ≫ leftExactCyclesComparison G S) ≫
        G.map S.homologyπ := (Category.assoc _ _ _).symm
    _ = (leftExactCyclesComparison F S ≫ τ.app S.cycles) ≫ G.map S.homologyπ :=
      congrArg (fun a => a ≫ G.map S.homologyπ)
        (leftExactCyclesComparison_naturality F S G τ)
    _ = leftExactCyclesComparison F S ≫ (τ.app S.cycles ≫ G.map S.homologyπ) :=
      Category.assoc _ _ _
    _ = leftExactCyclesComparison F S ≫ (F.map S.homologyπ ≫ τ.app S.homology) :=
      congrArg (fun a => leftExactCyclesComparison F S ≫ a) (τ.naturality S.homologyπ).symm
    _ = (leftExactCyclesComparison F S ≫ F.map S.homologyπ) ≫ τ.app S.homology :=
      (Category.assoc _ _ _).symm
    _ = ((S.map F).homologyπ ≫ leftExactHomologyEdge F S) ≫ τ.app S.homology :=
      congrArg (fun a => a ≫ τ.app S.homology)
        (leftExactHomologyEdge_characteristic F S).symm
    _ = _ := Category.assoc _ _ _

end Naturality

section ExactFunctor

variable [F.PreservesHomology]

/-- With actual homology preservation, the forward edge is the native comparison homomorphism. -/
theorem leftExactHomologyEdge_eq_mapHomologyIso_hom :
    leftExactHomologyEdge F S = (S.mapHomologyIso F).hom := by
  let c := KernelFork.ofι S.iCycles S.iCycles_g
  let h : IsLimit (c.map F) := KernelFork.mapIsLimit c S.cyclesIsKernel F
  let _ : Mono (F.map S.iCycles) := mono_of_isLimit_fork h
  have hCycles : leftExactCyclesComparison F S = (S.mapCyclesIso F).hom := by
    apply (cancel_mono (F.map S.iCycles)).mp
    exact (leftExactCyclesComparison_i F S).trans (S.mapCyclesIso_hom_iCycles F).symm
  apply (cancel_epi (S.map F).homologyπ).mp
  exact (leftExactHomologyEdge_characteristic F S).trans
    ((congrArg (fun z => z ≫ F.map S.homologyπ) hCycles).trans
      (homologyπ_comp_mapHomologyIso_hom S F).symm)

end ExactFunctor

end CategoryTheory.ShortComplex
