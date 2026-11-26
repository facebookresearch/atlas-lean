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
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Basic.UnivLE

/-!
# Tor boundaries of the boundary–cycle–homology sequence

Let R be an arbitrary ring, P a homological complex of right R-modules, and N a left R-module.
For i=c.prev(j), write B_j=image(d_P(i,j)), Z_j for cycles, and H_j for homology. The short
exact row 0→B_j→Z_j→H_j→0 gives the positive connecting map Tor₁^R(H_j,N)→B_j⊗_R N, followed by
the degree-zero derived-to-tensor comparison.

This map is killed by β_N:B_j⊗_R N→Z_j⊗_R N, and the Tor–tensor row is exact at B_j⊗_R N. If
tensoring with P_j and its outgoing differential image preserves homology, the cycle Tor₁
vanishes and the connecting map is mono. It then identifies Tor₁^R(H_j,N) with ker(β_N),
retaining the connecting map as the kernel-inclusion composite.

The core construction uses projective resolutions in both module categories at a common
coefficient universe. Lifting a right complex in v and a left coefficient in w to W=max(u,v,w,t)
gives independent-world factories at any further height t. The kernel factory tests the
tensor-exactness conditions on the lifted term and lifted outgoing image.
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

/-- Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. The map
δ:Tor₁^R(H_j,N)→B_j⊗_R N is the left-derived connecting morphism for the fixed-coefficient
tensor functor, followed by its canonical degree-zero tensor comparison. It is a morphism of
abelian groups. -/
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

/-- Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. The positive boundary
δ satisfies δ≫β_N=0 as a map Tor₁^R(H_j,N)→Z_j⊗_R N. -/
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
  let δ : (F.leftDerived 1).obj S.X₃ ⟶ (F.leftDerived 0).obj S.X₁ :=
    LeftDerivedDelta.LDdelta F 0 S hS
  let a₁ : (F.leftDerived 0).obj S.X₁ ⟶ F.obj S.X₁ := (e.app S.X₁).hom
  let a₂ : (F.leftDerived 0).obj S.X₂ ⟶ F.obj S.X₂ := (e.app S.X₂).hom
  have he : a₁ ≫ F.map S.f = (F.leftDerived 0).map S.f ≫ a₂ := by
    simpa only [a₁, a₂, NatIso.app_hom] using (e.hom.naturality S.f).symm
  change (δ ≫ a₁) ≫ F.map S.f = 0
  calc
    _ = δ ≫ (a₁ ≫ F.map S.f) := Category.assoc δ a₁ (F.map S.f)
    _ = δ ≫ ((F.leftDerived 0).map S.f ≫ a₂) := congrArg (fun z => δ ≫ z) he
    _ = (δ ≫ (F.leftDerived 0).map S.f) ≫ a₂ :=
      (Category.assoc δ ((F.leftDerived 0).map S.f) a₂).symm
    _ = 0 ≫ a₂ := congrArg (fun z => z ≫ a₂) hz
    _ = 0 := by simp only [zero_comp]

/-- Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. The short complex is
Tor₁^R(H_j,N) --δ→ B_j⊗_R N --β_N→ Z_j⊗_R N, with zero composite supplied by the connecting-map
relation. -/
def torBoundaryTensorSequence : ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (torBoundary R P N i j hi)
    (((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap P i j)).app N)
    (torBoundary_comp_boundaryTensor R P N i j hi)

/-- Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. The short complex δ
followed by β_N is exact at B_j⊗_R N: image(δ)=ker(β_N). The statement does not require tensor
exactness of P_j or the outgoing image. -/
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

/-- Let R be a ring in u, c a complex shape on I in κ, K,L right-module complexes of shape c and N a
left module in v, with projective resolutions in both module categories. For i=c.prev(j) and
φ:K→L, let B(φ):image(d_K(i,j))→image(d_L(i,j)) be its incoming-image map. Then
Tor₁^R(H_jφ,N)≫δ_L=δ_K≫(B(φ)⊗id_N). -/
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
  have he : (F.leftDerived 0).map ψ.τ₁ ≫ (e.app SL.X₁).hom =
      (e.app SK.X₁).hom ≫ F.map ψ.τ₁ := by
    simpa only [NatIso.app_hom] using e.hom.naturality ψ.τ₁
  rw [← h₃]
  change (F.leftDerived 1).map ψ.τ₃ ≫
      (LeftDerivedDelta.LDdelta F 0 SL hL ≫ (e.app SL.X₁).hom) =
    (LeftDerivedDelta.LDdelta F 0 SK hK ≫ (e.app SK.X₁).hom) ≫ F.map ψ.τ₁
  calc
    _ = (LeftDerivedDelta.LDdelta F 0 SK hK ≫ (F.leftDerived 0).map ψ.τ₁) ≫
        (e.app SL.X₁).hom := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ (e.app SL.X₁).hom) hδ
    _ = LeftDerivedDelta.LDdelta F 0 SK hK ≫
        ((F.leftDerived 0).map ψ.τ₁ ≫ (e.app SL.X₁).hom) :=
      Category.assoc (LeftDerivedDelta.LDdelta F 0 SK hK)
        ((F.leftDerived 0).map ψ.τ₁) ((e.app SL.X₁).hom)
    _ = LeftDerivedDelta.LDdelta F 0 SK hK ≫
        ((e.app SK.X₁).hom ≫ F.map ψ.τ₁) :=
      congrArg (fun z => LeftDerivedDelta.LDdelta F 0 SK hK ≫ z) he
    _ = _ :=
      (Category.assoc (LeftDerivedDelta.LDdelta F 0 SK hK)
        ((e.app SK.X₁).hom) (F.map ψ.τ₁)).symm

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

/-- Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. Assume the functors
P_j⊗_R(-) and image(d_P(j,c.next(j)))⊗_R(-), from left R-modules in v to abelian groups in v,
preserve homology. The cycle row 0→Z_j→P_j→image(d_P(j,c.next(j)))→0 gives Tor₁^R(Z_j,N)=0. The
long exact sequence then makes δ:Tor₁^R(H_j,N)→B_j⊗_R N mono. -/
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

/-- Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. Assume the functors
P_j⊗_R(-) and image(d_P(j,c.next(j)))⊗_R(-), from left R-modules in v to abelian groups in v,
preserve homology. The exact and monic connecting map gives E:Tor₁^R(H_j,N)≅ker(β_N). Its
forward morphism is the kernel lift of δ, with E.hom≫kernel.ι=δ. -/
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
  let : IsIso k := isIso_of_mono_of_epi k
  exact asIso k

/-- Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. Assume the functors
P_j⊗_R(-) and image(d_P(j,c.next(j)))⊗_R(-), from left R-modules in v to abelian groups in v,
preserve homology. For E:Tor₁^R(H_j,N)≅ker(β_N), one has E.hom≫kernel.ι(β_N)=δ. The canonical
inclusion into B_j⊗_R N retains the chosen connecting map. -/
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

/-- Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. Assume the functors
P_j⊗_R(-) and image(d_P(j,c.next(j)))⊗_R(-), from left R-modules in v to abelian groups in v,
preserve homology. For E:Tor₁^R(H_j,N)≅ker(β_N), E.inv≫δ=kernel.ι(β_N) as maps ker(β_N)→B_j⊗_R
N. -/
@[reassoc]
theorem torBoundaryKernelIso_inv_boundary :
    (torBoundaryKernelIso R P N i j hi).inv ≫ torBoundary R P N i j hi =
      kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N) := by
  rw [← torBoundaryKernelIso_hom_ι R P N i j hi]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Flat
end Resolutions

/-- Let R be a ring in u, c a complex shape on I in κ, P a right-module complex in v, and N a left
module in w. At any height t put W=max(u,v,w,t), and lift P termwise and N to W. For
i=c.prev(j), the factory gives δ:Tor₁^R(H_j(P̃),Ñ)→image(d_{P̃}(i,j))⊗_R Ñ. The complex shape
is unchanged. -/
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

/-- Let R be a ring in u, c a complex shape on I in κ, P a right-module complex in v, and N a left
module in w. At any height t, put W=max(u,v,w,t) and lift P,N termwise to P̃,Ñ in W. For
i=c.prev(j), assume tensoring with P̃_j and image(d_{P̃}(j,c.next(j))) preserves homology on
left modules in W. Then Tor₁^R(H_j(P̃),Ñ)≅ker(β_{Ñ}), where β is the incoming-boundary
inclusion into cycles of the lifted complex. -/
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
