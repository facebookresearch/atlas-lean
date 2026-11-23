/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.SigmaComponent
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusDeformation
public import MathlibExt.AlgebraicTopology.PlusConstruction.SquareAnnulusWinding
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Independently indexed original annulus groups

The literal sigma of lifted classical annuli has independent index and cell-lift universes.
Its radial normalizer retains every original index, normalized boundary vector and norm radius.
The original square-annulus perimeter in each summand has positive winding one and generates
its original based End group by integer powers.

At equal index and lift levels, the constructed normalizer identifies this literal sigma
with the existing `CellFamilyAttachment` annulus. The proved comparison sends each original
sigma inclusion to the existing component inclusion and sends the same perimeter to the
same original family path. The existing attachment space and attaching maps are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open scoped unitInterval

universe u v

namespace AlgebraicTopology.CellAnnulusComponents

/-- Radial coordinates of a literal annulus sigma, with independent index and cell-lift levels. -/
def rawCoordinates (ι : Type u) (n : ℕ) :
    (Σ _ : ι, TopPair.closedUnitBallAnnulus.{v} (Fin (n + 1) → ℝ)) ≃ₜ
      (Σ _ : ι, (classicalCellDiskPair.{v} (n + 1)).snd) × TopPair.cellAnnulusRadii := by
  let H := TopPair.closedUnitBallAnnulusSphereProd.{v} (Fin (n + 1) → ℝ)
  let e : (Σ _ : ι, TopPair.closedUnitBallAnnulus.{v} (Fin (n + 1) → ℝ)) ≃
      (Σ _ : ι, (classicalCellDiskPair.{v} (n + 1)).snd × TopPair.cellAnnulusRadii) :=
    Equiv.sigmaCongrRight (fun _ : ι => H.toEquiv)
  let h : (Σ _ : ι, TopPair.closedUnitBallAnnulus.{v} (Fin (n + 1) → ℝ)) ≃ₜ
      (Σ _ : ι, (classicalCellDiskPair.{v} (n + 1)).snd × TopPair.cellAnnulusRadii) :=
    { toEquiv := e
      continuous_toFun := by
        apply continuous_sigma
        intro i
        change Continuous (fun z : TopPair.closedUnitBallAnnulus.{v}
            (Fin (n + 1) → ℝ) => (Sigma.mk i (H z) :
              Σ _ : ι, (classicalCellDiskPair.{v} (n + 1)).snd × TopPair.cellAnnulusRadii))
        exact continuous_sigmaMk.comp H.continuous
      continuous_invFun := by
        apply continuous_sigma
        intro i
        change Continuous (fun z : (classicalCellDiskPair.{v} (n + 1)).snd ×
            TopPair.cellAnnulusRadii => (Sigma.mk i (H.symm z) :
              Σ _ : ι, TopPair.closedUnitBallAnnulus.{v} (Fin (n + 1) → ℝ)))
        exact continuous_sigmaMk.comp H.symm.continuous }
  exact h.trans (Homeomorph.sigmaProdDistrib
    (X := fun _ : ι => (classicalCellDiskPair.{v} (n + 1)).snd)
    (Y := TopPair.cellAnnulusRadii)).symm

/-- The coordinates preserve the original index and use its existing radial homeomorphism. -/
theorem rawCoordinates_apply (ι : Type u) (n : ℕ) (i : ι)
    (z : TopPair.closedUnitBallAnnulus.{v} (Fin (n + 1) → ℝ)) :
    rawCoordinates.{u, v} ι n (Sigma.mk i z) =
      ((⟨i, (TopPair.closedUnitBallAnnulusSphereProd.{v} (Fin (n + 1) → ℝ) z).1⟩ :
        Σ _ : ι, (classicalCellDiskPair.{v} (n + 1)).snd),
        (TopPair.closedUnitBallAnnulusSphereProd.{v} (Fin (n + 1) → ℝ) z).2) := rfl

/-- The inverse retains the original index and the same component inverse coordinates. -/
theorem rawCoordinates_symm_apply (ι : Type u) (n : ℕ)
    (p : (Σ _ : ι, (classicalCellDiskPair.{v} (n + 1)).snd) × TopPair.cellAnnulusRadii) :
    (rawCoordinates.{u, v} ι n).symm p =
      ⟨p.1.1, (TopPair.closedUnitBallAnnulusSphereProd.{v}
        (Fin (n + 1) → ℝ)).symm (p.1.2, p.2)⟩ := rfl

/-- Every original sigma index is preserved by normalization. -/
theorem rawCoordinates_index (ι : Type u) (n : ℕ)
    (z : Σ _ : ι, TopPair.closedUnitBallAnnulus.{v} (Fin (n + 1) → ℝ)) :
    (rawCoordinates.{u, v} ι n z).1.1 = z.1 := rfl

/-- The boundary coordinate is the normalized vector of the same original disk point. -/
theorem rawCoordinates_direction_val (ι : Type u) (n : ℕ)
    (z : Σ _ : ι, TopPair.closedUnitBallAnnulus.{v} (Fin (n + 1) → ℝ)) :
    (rawCoordinates.{u, v} ι n z).1.2.down.val =
      ‖z.2.1.down.val‖⁻¹ • z.2.1.down.val := by
  rcases z with ⟨i, z⟩
  change (TopPair.closedUnitBallAnnulusSphereProd.{v} (Fin (n + 1) → ℝ) z).1.down.val =
    ‖z.1.down.val‖⁻¹ • z.1.down.val
  exact TopPair.closedUnitBallAnnulusSphereProd_direction z

/-- The radius coordinate is exactly the norm of the original lifted disk point. -/
theorem rawCoordinates_radius_val (ι : Type u) (n : ℕ)
    (z : Σ _ : ι, TopPair.closedUnitBallAnnulus.{v} (Fin (n + 1) → ℝ)) :
    ((rawCoordinates.{u, v} ι n z).2 : ℝ) = ‖z.2.1.down.val‖ := by
  rcases z with ⟨i, z⟩
  exact TopPair.closedUnitBallAnnulusSphereProd_radius z

/-- The inverse coordinate map preserves the original index. -/
theorem rawCoordinates_symm_index (ι : Type u) (n : ℕ)
    (p : (Σ _ : ι, (classicalCellDiskPair.{v} (n + 1)).snd) × TopPair.cellAnnulusRadii) :
    ((rawCoordinates.{u, v} ι n).symm p).1 = p.1.1 := rfl

/-- The inverse scales the same original lifted boundary vector by the same radius. -/
theorem rawCoordinates_symm_val (ι : Type u) (n : ℕ)
    (p : (Σ _ : ι, (classicalCellDiskPair.{v} (n + 1)).snd) × TopPair.cellAnnulusRadii) :
    ((rawCoordinates.{u, v} ι n).symm p).2.1.down.val =
      (p.2 : ℝ) • p.1.2.down.val := by
  exact TopPair.closedUnitBallAnnulusSphereProd_symm_val (p.1.2, p.2)

/-- The literal original square-annulus basepoint in an independently indexed summand. -/
def rawBasepoint (ι : Type u) (i : ι) :
    Σ _ : ι, classicalCellSquareAnnulus.{v} :=
  Sigma.mk i classicalCellSquareAnnulusBasepoint.{v}

/-- The same original annular perimeter mapped by its actual sigma inclusion. -/
def rawPerimeter (ι : Type u) (i : ι) :
    Path (rawBasepoint.{u, v} ι i) (rawBasepoint.{u, v} ι i) :=
  classicalCellSquareAnnulusPerimeter.{v}.map
    (FundamentalGroupoid.SigmaComponent.inclusion
      (fun _ : ι => classicalCellSquareAnnulus.{v}) i).continuous

/-- Each original perimeter time retains the same index and annular point. -/
theorem rawPerimeter_apply (ι : Type u) (i : ι) (t : I) :
    rawPerimeter.{u, v} ι i t = Sigma.mk i (classicalCellSquareAnnulusPerimeter.{v} t) := rfl

/-- The mapped perimeter has the same original square direction and radius five-eighths. -/
theorem rawPerimeter_coordinates (ι : Type u) (i : ι) (t : I) :
    rawCoordinates.{u, v} ι 1 (rawPerimeter.{u, v} ι i t) =
      ((⟨i, classicalCellSquarePerimeter.{v} t⟩ : Σ _ : ι, classicalCellSquareBoundary.{v}),
        TopPair.cellAnnulusMidRadius) := by
  let H := TopPair.closedUnitBallAnnulusSphereProd.{v} (Fin 2 → ℝ)
  have h : H (classicalCellSquareAnnulusPerimeter.{v} t) =
      (classicalCellSquarePerimeter.{v} t, TopPair.cellAnnulusMidRadius) := by
    change H (H.symm (classicalCellSquarePerimeter.{v} t, TopPair.cellAnnulusMidRadius)) =
      (classicalCellSquarePerimeter.{v} t, TopPair.cellAnnulusMidRadius)
    exact H.apply_symm_apply (classicalCellSquarePerimeter.{v} t, TopPair.cellAnnulusMidRadius)
  exact (rawCoordinates_apply.{u, v} ι 1 i (classicalCellSquareAnnulusPerimeter.{v} t)).trans
    (congrArg
      (fun p : classicalCellSquareBoundary.{v} × TopPair.cellAnnulusRadii =>
        ((⟨i, p.1⟩ : Σ _ : ι, classicalCellSquareBoundary.{v}), p.2)) h)

/-- The actual perimeter class in the original End group of the independently sized sigma. -/
def rawPerimeterClass (ι : Type u) (i : ι) :
    FundamentalGroup (Σ _ : ι, classicalCellSquareAnnulus.{v}) (rawBasepoint.{u, v} ι i) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (rawPerimeter.{u, v} ι i))

/-- The existing original sigma End equivalence maps this same original perimeter to its class. -/
theorem rawComponent_perimeter (ι : Type u) (i : ι) :
    FundamentalGroup.sigmaComponentMulEquiv
        (fun _ : ι => classicalCellSquareAnnulus.{v}) i classicalCellSquareAnnulusBasepoint.{v}
        classicalCellSquareAnnulusPerimeterClass.{v} = rawPerimeterClass.{u, v} ι i := by
  let f := FundamentalGroupoid.SigmaComponent.inclusion
    (fun _ : ι => classicalCellSquareAnnulus.{v}) i
  have hClass : (Path.Homotopic.Quotient.mk classicalCellSquareAnnulusPerimeter.{v}).map f =
      Path.Homotopic.Quotient.mk (rawPerimeter.{u, v} ι i) :=
    (Path.Homotopic.Quotient.mk_map classicalCellSquareAnnulusPerimeter.{v} f).symm
  have hCast : ((Path.Homotopic.Quotient.mk
      classicalCellSquareAnnulusPerimeter.{v}).map f).cast rfl rfl =
        Path.Homotopic.Quotient.mk (rawPerimeter.{u, v} ι i) :=
    (Path.Homotopic.Quotient.cast_rfl_rfl _).trans hClass
  exact (FundamentalGroup.sigmaComponentMulEquiv_apply
    (fun _ : ι => classicalCellSquareAnnulus.{v}) i classicalCellSquareAnnulusBasepoint.{v}
    classicalCellSquareAnnulusPerimeterClass.{v}).trans
      ((FundamentalGroup.mapOfEq_apply f rfl classicalCellSquareAnnulusPerimeterClass.{v}).trans
        (congrArg FundamentalGroup.fromPath hCast))

/-- Winding on the original raw sigma End group, with independent index and cell levels. -/
def rawWindingIso (ι : Type u) (i : ι) :
    FundamentalGroup (Σ _ : ι, classicalCellSquareAnnulus.{v}) (rawBasepoint.{u, v} ι i) ≃*
      Multiplicative ℤ :=
  (FundamentalGroup.sigmaComponentMulEquiv
    (fun _ : ι => classicalCellSquareAnnulus.{v}) i
    classicalCellSquareAnnulusBasepoint.{v}).symm.trans classicalCellSquareAnnulusWindingIso.{v}

/-- The same mapped original perimeter has winding positive one. -/
theorem rawWindingIso_perimeter (ι : Type u) (i : ι) :
    rawWindingIso.{u, v} ι i (rawPerimeterClass.{u, v} ι i) = Multiplicative.ofAdd (1 : ℤ) := by
  let e := FundamentalGroup.sigmaComponentMulEquiv
    (fun _ : ι => classicalCellSquareAnnulus.{v}) i classicalCellSquareAnnulusBasepoint.{v}
  have h : e classicalCellSquareAnnulusPerimeterClass.{v} = rawPerimeterClass.{u, v} ι i :=
    rawComponent_perimeter.{u, v} ι i
  have hInv : e.symm (rawPerimeterClass.{u, v} ι i) =
      classicalCellSquareAnnulusPerimeterClass.{v} :=
    (congrArg e.symm h).symm.trans
      (e.symm_apply_apply classicalCellSquareAnnulusPerimeterClass.{v})
  exact (congrArg classicalCellSquareAnnulusWindingIso.{v} hInv).trans
    classicalCellSquareAnnulusWindingIso_perimeter.{v}

/-- Every original based class in a raw summand is an integer power of its same perimeter. -/
theorem raw_exists_perimeter_zpow (ι : Type u) (i : ι)
    (q : FundamentalGroup (Σ _ : ι, classicalCellSquareAnnulus.{v})
      (rawBasepoint.{u, v} ι i)) :
    ∃ n : ℤ, q = rawPerimeterClass.{u, v} ι i ^ n := by
  let e := FundamentalGroup.sigmaComponentMulEquiv
    (fun _ : ι => classicalCellSquareAnnulus.{v}) i classicalCellSquareAnnulusBasepoint.{v}
  obtain ⟨n, hn⟩ := classicalCellSquareAnnulus_exists_perimeter_zpow.{v} (e.symm q)
  refine ⟨n, ?_⟩
  have hImage : e (e.symm q) = e (classicalCellSquareAnnulusPerimeterClass.{v} ^ n) :=
    congrArg e hn
  have hPower : e (classicalCellSquareAnnulusPerimeterClass.{v} ^ n) =
      e classicalCellSquareAnnulusPerimeterClass.{v} ^ n :=
    map_zpow e classicalCellSquareAnnulusPerimeterClass.{v} n
  exact (e.apply_symm_apply q).symm.trans
    (hImage.trans (hPower.trans
      (congrArg
        (fun g : FundamentalGroup (Σ _ : ι, classicalCellSquareAnnulus.{v})
            (rawBasepoint.{u, v} ι i) => g ^ n)
        (rawComponent_perimeter.{u, v} ι i))))

/-- The independently constructed coordinates at equal levels give the original family annulus. -/
def sigmaToFamilyHomeomorph (ι : Type u) (n : ℕ) :
    (Σ _ : ι, TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) ≃ₜ
      CellCollarCover.annulus ι n :=
  (rawCoordinates.{u, u} ι n).trans (CellAnnulusCoordinates.homeomorph ι n).symm

/-- This actual comparison is the original component inclusion on each literal sigma summand. -/
theorem sigmaToFamilyHomeomorph_apply (ι : Type u) (n : ℕ) (i : ι)
    (z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) :
    sigmaToFamilyHomeomorph ι n (Sigma.mk i z) =
      CellAnnulusCoordinates.componentInclusion n i z := by
  let H := TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ)
  let p : CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii :=
    (⟨i, (H z).1⟩, (H z).2)
  have hMapped :
      (CellAnnulusCoordinates.homeomorph ι n).symm
          (rawCoordinates.{u, u} ι n (Sigma.mk i z)) =
        (CellAnnulusCoordinates.homeomorph ι n).symm p :=
    congrArg (CellAnnulusCoordinates.homeomorph ι n).symm
      (rawCoordinates_apply.{u, u} ι n i z)
  have hInverse : (CellAnnulusCoordinates.homeomorph ι n).symm p =
      CellAnnulusCoordinates.componentInclusion n i (H.symm (H z)) :=
    (CellAnnulusCoordinates.homeomorph_symm_apply n p).trans
      (CellAnnulusCoordinates.inverse_component n i (H z).1 (H z).2)
  exact hMapped.trans (hInverse.trans
    (congrArg (CellAnnulusCoordinates.componentInclusion n i) (H.symm_apply_apply z)))

/-- The actual sigma inclusion followed by the proved comparison is the original annular map. -/
theorem sigmaToFamily_inclusion (ι : Type u) (n : ℕ) (i : ι) :
    (sigmaToFamilyHomeomorph ι n).toHomotopyEquiv.toFun.comp
        (FundamentalGroupoid.SigmaComponent.inclusion
          (fun _ : ι => TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) i) =
      CellAnnulusCoordinates.componentInclusion n i := by
  apply ContinuousMap.ext
  intro z
  exact sigmaToFamilyHomeomorph_apply ι n i z

/-- The actual component functor is the original sigma functor followed by the comparison. -/
theorem componentFunctor_eq (ι : Type u) (n : ℕ) (i : ι) :
    FundamentalGroupoid.map (FundamentalGroupoid.SigmaComponent.inclusion
        (fun _ : ι => TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) i) ⋙
      FundamentalGroupoid.map (sigmaToFamilyHomeomorph ι n).toHomotopyEquiv.toFun =
        FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion n i) := by
  let f := FundamentalGroupoid.SigmaComponent.inclusion
    (fun _ : ι => TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) i
  let g := (sigmaToFamilyHomeomorph ι n).toHomotopyEquiv.toFun
  exact (FundamentalGroupoid.map_comp g f).symm.trans
    (congrArg
      (fun h : C(TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ),
          CellCollarCover.annulus ι n) => FundamentalGroupoid.map h)
      (sigmaToFamily_inclusion ι n i))

/-- The constructed raw-to-family homeomorphism gives full faithfulness on original groupoids. -/
def sigmaToFamilyFullyFaithful (ι : Type u) (n : ℕ) :
    (FundamentalGroupoid.map (sigmaToFamilyHomeomorph ι n).toHomotopyEquiv.toFun).FullyFaithful :=
  by
    let G := FundamentalGroupoid.map (sigmaToFamilyHomeomorph ι n).toHomotopyEquiv.toFun
    let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
      (sigmaToFamilyHomeomorph ι n).toHomotopyEquiv
    let _ : G.IsEquivalence := by exact E.isEquivalence_functor
    exact Functor.FullyFaithful.ofFullyFaithful G

/-- The original component inclusion is fully faithful at arbitrary original endpoints. -/
def componentFullyFaithful (ι : Type u) (n : ℕ) (i : ι) :
    (FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion n i)).FullyFaithful :=
  ((FundamentalGroupoid.SigmaComponent.fullyFaithful
    (fun _ : ι => TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) i).comp
      (sigmaToFamilyFullyFaithful ι n)).ofIso (eqToIso (componentFunctor_eq ι n i))

/-- The concrete preimage uses both original preimages and the proved equality transports. -/
theorem componentFullyFaithful_preimage (ι : Type u) (n : ℕ) (i : ι)
    {a b : FundamentalGroupoid (TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ))}
    (q : (FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion n i)).obj a ⟶
      (FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion n i)).obj b) :
    (componentFullyFaithful ι n i).preimage q =
      (FundamentalGroupoid.SigmaComponent.fullyFaithful
        (fun _ : ι => TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) i).preimage
          ((sigmaToFamilyFullyFaithful ι n).preimage
            ((eqToIso (componentFunctor_eq ι n i)).hom.app a ≫ q ≫
              (eqToIso (componentFunctor_eq ι n i)).inv.app b)) := rfl

/-- Mapping the constructed preimage by the original component map recovers the same arrow. -/
theorem componentFullyFaithful_map_preimage (ι : Type u) (n : ℕ) (i : ι)
    {a b : FundamentalGroupoid (TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ))}
    (q : (FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion n i)).obj a ⟶
      (FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion n i)).obj b) :
    (FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion n i)).map
        ((componentFullyFaithful ι n i).preimage q) = q :=
  (componentFullyFaithful ι n i).map_preimage q

/-- Preimage after the original component map recovers the same original component arrow. -/
theorem componentFullyFaithful_preimage_map (ι : Type u) (n : ℕ) (i : ι)
    {a b : FundamentalGroupoid (TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ))}
    (q : a ⟶ b) :
    (componentFullyFaithful ι n i).preimage
        ((FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion n i)).map q) = q :=
  (componentFullyFaithful ι n i).preimage_map q

/-- The original based End equivalence of an actual component inclusion in the existing family. -/
def componentMulEquiv (ι : Type u) (n : ℕ) (i : ι)
    (z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) :
    FundamentalGroup (TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) z ≃*
      FundamentalGroup (CellCollarCover.annulus ι n)
        (CellAnnulusCoordinates.componentInclusion n i z) :=
  (componentFullyFaithful ι n i).mulEquivEnd (FundamentalGroupoid.mk z)

/-- Its forward map is precisely the original equality-pointed component-inclusion map. -/
theorem componentMulEquiv_apply (ι : Type u) (n : ℕ) (i : ι)
    (z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ))
    (q : FundamentalGroup (TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) z) :
    componentMulEquiv ι n i z q =
      FundamentalGroup.mapOfEq (CellAnnulusCoordinates.componentInclusion n i) rfl q := by
  let j := CellAnnulusCoordinates.componentInclusion n i
  change FundamentalGroup.map j z q = FundamentalGroup.mapOfEq j rfl q
  exact (congrArg
    (fun f : FundamentalGroup (TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) z →*
        FundamentalGroup (CellCollarCover.annulus ι n) (j z) => f q)
    (FundamentalGroup.mapOfEq_rfl j z)).symm

/-- The original single-component section is the same section in the existing indexed annulus. -/
theorem componentInclusion_section (ι : Type u) (i : ι)
    (b : classicalCellSquareBoundary.{u}) :
    CellAnnulusDeformation.boundarySection ι 1
        (⟨i, b⟩ : CellFamilyAttachment.boundaries ι 1) =
      CellAnnulusCoordinates.componentInclusion 1 i (classicalCellSquareAnnulusSection.{u} b) :=
  (CellAnnulusDeformation.boundarySection_coordinates 1
    (⟨i, b⟩ : CellFamilyAttachment.boundaries ι 1)).trans
      (CellAnnulusCoordinates.inverse_component 1 i b TopPair.cellAnnulusMidRadius)

/-- The original annular basepoint in its actual selected family summand. -/
def basepoint (ι : Type u) (i : ι) : CellCollarCover.annulus ι 1 :=
  CellAnnulusCoordinates.componentInclusion 1 i classicalCellSquareAnnulusBasepoint.{u}

/-- The same original annular perimeter mapped by the existing component inclusion. -/
def perimeter (ι : Type u) (i : ι) : Path (basepoint ι i) (basepoint ι i) :=
  classicalCellSquareAnnulusPerimeter.{u}.map
    (CellAnnulusCoordinates.componentInclusion 1 i).continuous

/-- Its original point at each time is the same point in the existing family boundary section. -/
theorem perimeter_apply (ι : Type u) (i : ι) (t : I) :
    perimeter ι i t = CellAnnulusDeformation.boundarySection ι 1
      (⟨i, classicalCellSquarePerimeter.{u} t⟩ : CellFamilyAttachment.boundaries ι 1) :=
  (componentInclusion_section ι i (classicalCellSquarePerimeter.{u} t)).symm

/-- The actual original family perimeter class, in its original based End group. -/
def perimeterClass (ι : Type u) (i : ι) :
    FundamentalGroup (CellCollarCover.annulus ι 1) (basepoint ι i) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (perimeter ι i))

/-- The constructed comparison maps the literal raw basepoint to the original family basepoint. -/
theorem sigmaToFamily_basepoint (ι : Type u) (i : ι) :
    sigmaToFamilyHomeomorph ι 1 (rawBasepoint.{u, u} ι i) = basepoint ι i :=
  sigmaToFamilyHomeomorph_apply ι 1 i classicalCellSquareAnnulusBasepoint.{u}

/-- The actual map and both original endpoint casts carry the same raw perimeter to the family. -/
theorem sigmaToFamily_perimeter (ι : Type u) (i : ι) :
    ((rawPerimeter.{u, u} ι i).map
        (sigmaToFamilyHomeomorph ι 1).toHomotopyEquiv.toFun.continuous).cast
        (sigmaToFamily_basepoint ι i).symm (sigmaToFamily_basepoint ι i).symm =
      perimeter ι i := by
  apply Path.ext
  funext t
  change sigmaToFamilyHomeomorph ι 1 (rawPerimeter.{u, u} ι i t) =
    CellAnnulusCoordinates.componentInclusion 1 i (classicalCellSquareAnnulusPerimeter.{u} t)
  exact (congrArg (sigmaToFamilyHomeomorph ι 1) (rawPerimeter_apply.{u, u} ι i t)).trans
    (sigmaToFamilyHomeomorph_apply ι 1 i (classicalCellSquareAnnulusPerimeter.{u} t))

/-- The same equality-pointed original End map carries the literal raw class to the family class. -/
theorem sigmaToFamily_perimeterClass (ι : Type u) (i : ι) :
    FundamentalGroup.mulEquivOfHomeomorphAt (sigmaToFamilyHomeomorph ι 1)
        (rawBasepoint.{u, u} ι i) (basepoint ι i) (sigmaToFamily_basepoint ι i)
        (rawPerimeterClass.{u, u} ι i) = perimeterClass ι i := by
  let f := (sigmaToFamilyHomeomorph ι 1).toHomotopyEquiv.toFun
  have hClass :
      ((Path.Homotopic.Quotient.mk (rawPerimeter.{u, u} ι i)).map f).cast
        (sigmaToFamily_basepoint ι i).symm (sigmaToFamily_basepoint ι i).symm =
          Path.Homotopic.Quotient.mk (perimeter ι i) :=
    (congrArg
      (fun q : Path.Homotopic.Quotient
          (f (rawBasepoint.{u, u} ι i)) (f (rawBasepoint.{u, u} ι i)) =>
        q.cast (sigmaToFamily_basepoint ι i).symm (sigmaToFamily_basepoint ι i).symm)
      (Path.Homotopic.Quotient.mk_map (rawPerimeter.{u, u} ι i) f).symm).trans
        ((Path.Homotopic.Quotient.mk_cast ((rawPerimeter.{u, u} ι i).map f.continuous)
          (sigmaToFamily_basepoint ι i).symm (sigmaToFamily_basepoint ι i).symm).symm.trans
            (congrArg Path.Homotopic.Quotient.mk (sigmaToFamily_perimeter ι i)))
  exact (FundamentalGroup.mulEquivOfHomeomorphAt_apply (sigmaToFamilyHomeomorph ι 1)
    (rawBasepoint.{u, u} ι i) (basepoint ι i) (sigmaToFamily_basepoint ι i)
    (rawPerimeterClass.{u, u} ι i)).trans
      ((FundamentalGroup.mapOfEq_apply f (sigmaToFamily_basepoint ι i)
        (rawPerimeterClass.{u, u} ι i)).trans (congrArg FundamentalGroup.fromPath hClass))

/-- The actual component equivalence carries its original perimeter to the same family class. -/
theorem componentMulEquiv_perimeter (ι : Type u) (i : ι) :
    componentMulEquiv ι 1 i classicalCellSquareAnnulusBasepoint.{u}
        classicalCellSquareAnnulusPerimeterClass.{u} = perimeterClass ι i := by
  let j := CellAnnulusCoordinates.componentInclusion 1 i
  have hClass : (Path.Homotopic.Quotient.mk classicalCellSquareAnnulusPerimeter.{u}).map j =
      Path.Homotopic.Quotient.mk (perimeter ι i) :=
    (Path.Homotopic.Quotient.mk_map classicalCellSquareAnnulusPerimeter.{u} j).symm
  have hCast : ((Path.Homotopic.Quotient.mk
      classicalCellSquareAnnulusPerimeter.{u}).map j).cast rfl rfl =
        Path.Homotopic.Quotient.mk (perimeter ι i) :=
    (Path.Homotopic.Quotient.cast_rfl_rfl _).trans hClass
  exact (componentMulEquiv_apply ι 1 i classicalCellSquareAnnulusBasepoint.{u}
    classicalCellSquareAnnulusPerimeterClass.{u}).trans
      ((FundamentalGroup.mapOfEq_apply j rfl classicalCellSquareAnnulusPerimeterClass.{u}).trans
        (congrArg FundamentalGroup.fromPath hCast))

/-- Winding in the existing actual family, transported through the proved raw comparison. -/
def windingIso (ι : Type u) (i : ι) :
    FundamentalGroup (CellCollarCover.annulus ι 1) (basepoint ι i) ≃* Multiplicative ℤ :=
  (FundamentalGroup.mulEquivOfHomeomorphAt (sigmaToFamilyHomeomorph ι 1)
    (rawBasepoint.{u, u} ι i) (basepoint ι i) (sigmaToFamily_basepoint ι i)).symm.trans
      (rawWindingIso.{u, u} ι i)

/-- The same actual family perimeter has positive winding one. -/
theorem windingIso_perimeter (ι : Type u) (i : ι) :
    windingIso ι i (perimeterClass ι i) = Multiplicative.ofAdd (1 : ℤ) := by
  let e := FundamentalGroup.mulEquivOfHomeomorphAt (sigmaToFamilyHomeomorph ι 1)
    (rawBasepoint.{u, u} ι i) (basepoint ι i) (sigmaToFamily_basepoint ι i)
  have h : e (rawPerimeterClass.{u, u} ι i) = perimeterClass ι i :=
    sigmaToFamily_perimeterClass ι i
  have hInv : e.symm (perimeterClass ι i) = rawPerimeterClass.{u, u} ι i :=
    (congrArg e.symm h).symm.trans (e.symm_apply_apply (rawPerimeterClass.{u, u} ι i))
  exact (congrArg (rawWindingIso.{u, u} ι i) hInv).trans (rawWindingIso_perimeter.{u, u} ι i)

/-- Every original actual-family based class is an integer power of its same perimeter. -/
theorem exists_perimeter_zpow (ι : Type u) (i : ι)
    (q : FundamentalGroup (CellCollarCover.annulus ι 1) (basepoint ι i)) :
    ∃ n : ℤ, q = perimeterClass ι i ^ n := by
  let e := FundamentalGroup.mulEquivOfHomeomorphAt (sigmaToFamilyHomeomorph ι 1)
    (rawBasepoint.{u, u} ι i) (basepoint ι i) (sigmaToFamily_basepoint ι i)
  obtain ⟨n, hn⟩ := raw_exists_perimeter_zpow.{u, u} ι i (e.symm q)
  refine ⟨n, ?_⟩
  have hImage : e (e.symm q) = e (rawPerimeterClass.{u, u} ι i ^ n) := congrArg e hn
  have hPower : e (rawPerimeterClass.{u, u} ι i ^ n) =
      e (rawPerimeterClass.{u, u} ι i) ^ n :=
    map_zpow e (rawPerimeterClass.{u, u} ι i) n
  exact (e.apply_symm_apply q).symm.trans
    (hImage.trans (hPower.trans
      (congrArg
        (fun g : FundamentalGroup (CellCollarCover.annulus ι 1) (basepoint ι i) => g ^ n)
        (sigmaToFamily_perimeterClass ι i))))

end AlgebraicTopology.CellAnnulusComponents

end

end
