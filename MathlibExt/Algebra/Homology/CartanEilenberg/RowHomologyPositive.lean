/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.Bicomplex
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowSplittings
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex

/-!
# Positive row homology of a Cartan–Eilenberg resolution

Let P be Cartan–Eilenberg data for a nonnegative complex L in an abelian category. In positive
original degree q+1, the cycles and homology of its fixed-resolution row a identify with
PC_{q+1,a} and PH_{q+1,a}.

The homology coordinates commute with the resolution differentials. Consequently the
vertical-homology complex in original degree q+1 is isomorphic to PH_{q+1}.complex and is a
projective resolution of H_{q+1}(L).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.CartanEilenbergResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. For
a,q ∈ ℕ, the original-degree short complex in the fixed-resolution row at (q+2,q+1,q) has left
homology data with cycles term PC_{q+1,a} and homology term PH_{q+1,a}, using the stored
horseshoe inclusion and projection. -/
noncomputable def cartanEilenbergRowHomologySuccLeftData (a q : ℕ) :
    ((P.bicomplex.X a).sc' (q + 2) (q + 1) q).LeftHomologyData := by
  let S₀ := (P.bicomplex.X a).sc' (q + 2) (q + 1) q
  let tI := (P.termHorseshoe (q + 1)).i.f a
  let tP := (P.termHorseshoe (q + 1)).p.f a
  let cI := (P.cyclesHorseshoe q).i.f a
  let tI₀ := (P.termHorseshoe q).i.f a
  let tPnext := (P.termHorseshoe (q + 2)).p.f a
  let cIcur := (P.cyclesHorseshoe (q + 1)).i.f a
  let cPcur := (P.cyclesHorseshoe (q + 1)).p.f a
  letI : Mono tI := (P.termComponentSplitting a (q + 1)).mono_f
  letI : Mono cI := (P.cyclesComponentSplitting a q).mono_f
  letI : Mono tI₀ := (P.termComponentSplitting a q).mono_f
  letI : Mono (cI ≫ tI₀) := inferInstance
  letI : Epi tPnext := (P.termComponentSplitting a (q + 2)).epi_g
  have hfactor : S₀.g = tP ≫ (cI ≫ tI₀) := by
    dsimp only [S₀, tP, cI, tI₀]
    change (P.bicomplex.X a).d (q + 1) q = _
    rw [P.bicomplex_d₂ a q]
    rfl
  have wi : tI ≫ S₀.g = 0 := by
    rw [hfactor, ← Category.assoc]
    change ((P.termComponentShortComplex a (q + 1)).f ≫
      (P.termComponentShortComplex a (q + 1)).g) ≫ (cI ≫ tI₀) = 0
    rw [(P.termComponentShortComplex a (q + 1)).zero, zero_comp]
  let hi₀ := (P.termComponentSplitting a (q + 1)).fIsKernel
  let hi : IsLimit (KernelFork.ofι tI wi) := by
    exact Limits.isKernelCompMono hi₀ (cI ≫ tI₀) hfactor
  let f' := hi.lift (KernelFork.ofι S₀.f S₀.zero)
  have hf' : f' = tPnext ≫ cIcur := by
    dsimp only [f']
    apply (cancel_mono tI).1
    calc
      hi.lift (KernelFork.ofι S₀.f S₀.zero) ≫ tI = S₀.f := by
        change hi.lift (KernelFork.ofι S₀.f S₀.zero) ≫
            Fork.ι (KernelFork.ofι tI wi) =
          Fork.ι (KernelFork.ofι S₀.f S₀.zero)
        exact Fork.IsLimit.lift_ι hi
      _ = tPnext ≫ (cIcur ≫ tI) := by
        dsimp only [S₀, tI, tPnext, cIcur]
        change (P.bicomplex.X a).d (q + 2) (q + 1) =
          (P.termHorseshoe (q + 2)).p.f a ≫
            ((P.cyclesHorseshoe (q + 1)).i.f a ≫
              (P.termHorseshoe (q + 1)).i.f a)
        rw [P.bicomplex_d₂ a (q + 1)]
        rfl
      _ = (tPnext ≫ cIcur) ≫ tI := (Category.assoc _ _ _).symm
  have wπ : f' ≫ cPcur = 0 := by
    rw [hf']
    dsimp only [tPnext, cIcur, cPcur]
    rw [Category.assoc]
    change (P.termHorseshoe (q + 2)).p.f a ≫
      ((P.cyclesComponentShortComplex a (q + 1)).f ≫
        (P.cyclesComponentShortComplex a (q + 1)).g) = 0
    rw [(P.cyclesComponentShortComplex a (q + 1)).zero, comp_zero]
  let hπ₀ := (P.cyclesComponentSplitting a (q + 1)).gIsCokernel
  let hπ : IsColimit (CokernelCofork.ofπ cPcur wπ) := by
    exact Limits.isCokernelEpiComp hπ₀ tPnext hf'
  exact
    { K := (P.cyclesResolution (q + 1)).complex.X a
      H := (P.homologyResolution (q + 1)).complex.X a
      i := tI
      π := cPcur
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hπ }

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. For
every a,q ∈ ℕ, the cycles in original degree q+1 of the row P.bicomplex.Xₐ are canonically
isomorphic to PC_{q+1,a}. -/
noncomputable def cartanEilenbergRowCyclesSuccIso (a q : ℕ) :
    (P.bicomplex.X a).cycles (q + 1) ≅
      (P.cyclesResolution (q + 1)).complex.X a :=
  (P.bicomplex.X a).cyclesIsoSc' (q + 2) (q + 1) q
      (by simp) (by simp) ≪≫
    (P.cartanEilenbergRowHomologySuccLeftData a q).cyclesIso

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. For
every a,q ∈ ℕ, H_{q+1}(P.bicomplex.Xₐ) is canonically isomorphic to PH_{q+1,a}, the
resolution-degree-a homology-resolution term. -/
noncomputable def cartanEilenbergRowHomologySuccIso (a q : ℕ) :
    (P.bicomplex.X a).homology (q + 1) ≅
      (P.homologyResolution (q + 1)).complex.X a :=
  (P.bicomplex.X a).homologyIsoSc' (q + 2) (q + 1) q
      (by simp) (by simp) ≪≫
    (P.cartanEilenbergRowHomologySuccLeftData a q).homologyIso

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. In
original degree q+1 and resolution degree a, the homology quotient followed by H_{q+1}(rowₐ) ≅
PH_{q+1,a} equals the cycle identification with PC_{q+1,a} followed by the cycle-horseshoe
projection to PH_{q+1,a}. -/
@[reassoc]
theorem homologyπ_comp_cartanEilenbergRowHomologySuccIso_hom (a q : ℕ) :
    (P.bicomplex.X a).homologyπ (q + 1) ≫
        (P.cartanEilenbergRowHomologySuccIso a q).hom =
      (P.cartanEilenbergRowCyclesSuccIso a q).hom ≫
        (P.cyclesHorseshoe (q + 1)).p.f a := by
  dsimp only [cartanEilenbergRowHomologySuccIso,
    cartanEilenbergRowCyclesSuccIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. The
coordinates H_{q+1}(rowₐ) ≅ PH_{q+1,a} commute with the resolution differential a+1 → a: the
homology map of that bicomplex differential corresponds to the differential of PH_{q+1}. -/
@[reassoc]
theorem cartanEilenbergRowHomologySuccIso_naturality (a q : ℕ) :
    HomologicalComplex.homologyMap (P.bicomplex.d (a + 1) a) (q + 1) ≫
        (P.cartanEilenbergRowHomologySuccIso a q).hom =
      (P.cartanEilenbergRowHomologySuccIso (a + 1) q).hom ≫
        (P.homologyResolution (q + 1)).complex.d (a + 1) a := by
  let φ := P.bicomplex.d (a + 1) a
  let ψ := (HomologicalComplex.shortComplexFunctor' C
    (ComplexShape.down ℕ) (q + 2) (q + 1) q).map φ
  let hSrc := P.cartanEilenbergRowHomologySuccLeftData (a + 1) q
  let hTgt := P.cartanEilenbergRowHomologySuccLeftData a q
  let γ := ShortComplex.leftHomologyMapData ψ hSrc hTgt
  have hK : γ.φK =
      (P.cyclesResolution (q + 1)).complex.d (a + 1) a := by
    apply (cancel_mono hTgt.i).1
    rw [γ.commi]
    dsimp only [hSrc, hTgt, ψ, φ,
      cartanEilenbergRowHomologySuccLeftData]
    change (P.termHorseshoe (q + 1)).i.f (a + 1) ≫
        (P.termResolution (q + 1)).complex.d (a + 1) a =
      (P.cyclesResolution (q + 1)).complex.d (a + 1) a ≫
        (P.termHorseshoe (q + 1)).i.f a
    exact (P.termHorseshoe (q + 1)).i.comm (a + 1) a
  have hH : γ.φH =
      (P.homologyResolution (q + 1)).complex.d (a + 1) a := by
    apply (cancel_epi hSrc.π).1
    rw [γ.commπ, hK]
    dsimp only [hSrc, hTgt,
      cartanEilenbergRowHomologySuccLeftData]
    exact ((P.cyclesHorseshoe (q + 1)).p.comm (a + 1) a).symm
  dsimp only [cartanEilenbergRowHomologySuccIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [HomologicalComplex.homologyIsoSc'_hom_naturality_assoc
    φ (q + 2) (q + 1) q (by simp) (by simp)]
  rw [γ.homologyMap_comm, hH]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. For q
∈ ℕ, the resolution-direction vertical-homology complex in original degree q+1 is isomorphic to
the stored homology resolution PH_{q+1}.complex. -/
noncomputable def cartanEilenbergVerticalHomologySuccComplexIso (q : ℕ) :
    P.bicomplex.verticalHomologyComplex (q + 1) ≅
      (P.homologyResolution (q + 1)).complex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun a => P.cartanEilenbergRowHomologySuccIso a q)
    (fun i j hij => by
      obtain rfl : j + 1 = i := hij
      simpa only [HomologicalComplex₂.verticalHomologyComplex_X,
        HomologicalComplex₂.verticalHomologyComplex_d] using
        (P.cartanEilenbergRowHomologySuccIso_naturality j q).symm)

@[simp]
theorem cartanEilenbergVerticalHomologySuccComplexIso_hom_f (a q : ℕ) :
    (P.cartanEilenbergVerticalHomologySuccComplexIso q).hom.f a =
      (P.cartanEilenbergRowHomologySuccIso a q).hom :=
  rfl

@[simp]
theorem cartanEilenbergVerticalHomologySuccComplexIso_inv_f (a q : ℕ) :
    (P.cartanEilenbergVerticalHomologySuccComplexIso q).inv.f a =
      (P.cartanEilenbergRowHomologySuccIso a q).inv :=
  rfl

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. For
each q ∈ ℕ, the vertical-homology complex in original degree q+1, with augmentation transported
from PH_{q+1}, is a projective resolution of H_{q+1}(L). -/
noncomputable def cartanEilenbergVerticalHomologySuccResolution (q : ℕ) :
    ProjectiveResolution (L.homology (q + 1)) where
  complex := P.bicomplex.verticalHomologyComplex (q + 1)
  projective a := Projective.of_iso
    (P.cartanEilenbergRowHomologySuccIso a q).symm
    ((P.homologyResolution (q + 1)).projective a)
  π := (P.cartanEilenbergVerticalHomologySuccComplexIso q).hom ≫
    (P.homologyResolution (q + 1)).π
  quasiIso := by infer_instance

@[simp]
theorem cartanEilenbergVerticalHomologySuccResolution_complex (q : ℕ) :
    (P.cartanEilenbergVerticalHomologySuccResolution q).complex =
      P.bicomplex.verticalHomologyComplex (q + 1) :=
  rfl

@[simp]
theorem cartanEilenbergVerticalHomologySuccResolution_π (q : ℕ) :
    (P.cartanEilenbergVerticalHomologySuccResolution q).π =
      (P.cartanEilenbergVerticalHomologySuccComplexIso q).hom ≫
        (P.homologyResolution (q + 1)).π :=
  rfl

end HomologicalComplex.CartanEilenbergResolution

end
