/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
# Homology edge for a left-exact functor

Let C and D be categories with zero morphisms, F:C → D preserve zero
morphisms and finite limits, and S be a short complex whose homology,
and the homology of its termwise F-image, are chosen.
Preservation of the cycles kernel gives the canonical isomorphism
γ:Z(F(S)) ≅ F(Z(S)).

The composite F(q_S)∘γ, where q_S is the cycles-to-homology projection,
annihilates boundaries and induces the edge
ε:H(F(S)) → F(H(S)).
Its defining equation is ε∘q_{F(S)}=F(q_S)∘γ.
The comparison and edge are natural in short-complex morphisms and in
natural transformations between such functors. If F preserves homology,
the edge equals the forward map of the canonical homology isomorphism.
The two categories have independent object and morphism universes.
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

/-- Let C and D have zero morphisms, and let F:C → D preserve zero
morphisms and finite limits. Let S be a short complex with chosen
homology, and assume S mapped by F also has its chosen homology.

The canonical cycles comparison γ:Z(F(S)) → F(Z(S)), induced by the preserved kernel of the second
differential of S. -/
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

/-- Let C and D have zero morphisms, and let F:C → D preserve zero
morphisms and finite limits. Let S be a short complex with chosen
homology, and assume S mapped by F also has its chosen homology.

The canonical comparison γ:Z(F(S)) → F(Z(S)) is an isomorphism, since F preserves the cycles kernel.
-/
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

/-- Let C and D have zero morphisms, and let F:C → D preserve zero
morphisms and finite limits. Let S be a short complex with chosen
homology, and assume S mapped by F also has its chosen homology.

The canonical cycles isomorphism Z(F(S)) ≅ F(Z(S)) whose forward map is the preserved-kernel
comparison. -/
def leftExactCyclesComparisonIso : (S.map F).cycles ≅ F.obj S.cycles :=
  asIso (leftExactCyclesComparison F S)

/-- Let C and D have zero morphisms, and let F:C → D preserve zero
morphisms and finite limits. Let S be a short complex with chosen
homology, and assume S mapped by F also has its chosen homology.

The forward map of Z(F(S)) ≅ F(Z(S)) is exactly the canonical cycles comparison γ. -/
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

/-- Let C and D have zero morphisms, and let F:C → D preserve zero
morphisms and finite limits. Let S be a short complex with chosen
homology, and assume S mapped by F also has its chosen homology.

The homology edge ε:H(F(S)) → F(H(S)) induced by F(q_S)∘γ on cycles, where q_S:Z(S) → H(S) is the
homology projection. -/
def leftExactHomologyEdge : (S.map F).homology ⟶ F.obj S.homology :=
  (S.map F).descHomology (leftExactCyclesComparison F S ≫ F.map S.homologyπ)
    (leftExactHomologyEdge_kills_boundaries F S)

/-- Let C and D have zero morphisms, and let F:C → D preserve zero
morphisms and finite limits. Let S be a short complex with chosen
homology, and assume S mapped by F also has its chosen homology.

For γ:Z(F(S)) → F(Z(S)), q_S and q_{F(S)} the homology projections, the edge satisfies
ε∘q_{F(S)}=F(q_S)∘γ. -/
theorem leftExactHomologyEdge_characteristic :
    (S.map F).homologyπ ≫ leftExactHomologyEdge F S =
      leftExactCyclesComparison F S ≫ F.map S.homologyπ :=
  (S.map F).π_descHomology _ _

section ComplexMorphism

variable (T : ShortComplex C) [T.HasHomology] [(T.map F).HasHomology] (φ : S ⟶ T)

/-- Let C,D have zero morphisms and F:C → D preserve zero morphisms and
finite limits. For a short-complex morphism φ:S → T, choose homology
of S,T and both F-images. The cycles comparisons satisfy
γ_T∘Z(F(φ))=F(Z(φ))∘γ_S. -/
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

/-- Let C,D have zero morphisms and F:C → D preserve zero morphisms and
finite limits. For a short-complex morphism φ:S → T, choose homology
of S,T and their F-images. The homology edges satisfy
ε_T∘H(F(φ))=F(H(φ))∘ε_S. -/
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
      congrArg (· ≫ F.map (ShortComplex.homologyMap φ)) (leftExactHomologyEdge_characteristic F
      S).symm
    _ = _ := Category.assoc _ _ _

end ComplexMorphism

section Naturality

variable (G : C ⥤ D) [G.PreservesZeroMorphisms] [PreservesFiniteLimits G]
variable [(S.map G).HasHomology] (τ : F ⟶ G)

/-- Let C,D have zero morphisms, let F,G:C → D preserve zero morphisms
and finite limits, and τ:F → G be natural. For a short complex S with
chosen homology of S,F(S),G(S), the cycles comparisons satisfy
γ_G∘Z(τ_S)=τ_{Z(S)}∘γ_F. -/
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

/-- Let C,D have zero morphisms, let F,G:C → D preserve zero morphisms
and finite limits, and τ:F → G be natural. For a short complex S with
chosen homology of S,F(S),G(S), the edges satisfy
ε_G∘H(τ_S)=τ_{H(S)}∘ε_F. -/
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

/-- Let C and D have zero morphisms, and let F:C → D preserve zero
morphisms and finite limits. Let S be a short complex with chosen
homology, and assume S mapped by F also has its chosen homology.

If F also preserves homology, its edge H(F(S)) → F(H(S)) equals the forward map of the canonical
homology comparison isomorphism. -/
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
