/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HiggsSmoothRealizationModels
public import MathlibExt.AlgebraicGeometry.HiggsKernelComparisonModels
public import MathlibExt.AlgebraicGeometry.HiggsReconstructionIsomorphisms
public import MathlibExt.AlgebraicGeometry.ManifoldRationalChernModels

/-!
# Wanted normalized compact Kähler Higgs correspondence

The standing scope is a connected compact Kähler complex manifold.
Source: Simpson, alg-geom/9604005v1, section 2 and Theorem2.3, pp7--11.
Arbitrary dimensions and ranks, all actual coherent theta-invariant
subsheaves, and all positive rational Chern classes are retained.

Every geometric realization uses the native smooth scalar extension of
the same holomorphic module, actual tensor coordinates and actual theta.
The forward object is the exact bar kernel. Metric independence produces
an actual Higgs isomorphism whose smooth scalar extension is parallel
for the original connection. Polystability and metric existence remain
proof/construction conclusions.
-/

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.CoordinateFormIntegrals
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicSheafHiggsModels
open MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels
open MathlibExt.AlgebraicGeometry.CoherentKahlerHiggsStability
open MathlibExt.AlgebraicGeometry.HiggsSmoothRealizationModels
open MathlibExt.AlgebraicGeometry.HiggsKernelComparisonModels
open MathlibExt.AlgebraicGeometry.HiggsReconstructionIsomorphisms
open MathlibExt.AlgebraicGeometry.HarmonicChernWeilFormulas
open MathlibExt.AlgebraicGeometry.SmoothManifoldSingularModels
open MathlibExt.AlgebraicGeometry.RealDeRhamSingularModels
open MathlibExt.AlgebraicGeometry.ManifoldRationalChernModels
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Native smooth-function inclusion preserves every actual holomorphic function value. -/
def_wanted native_holomorphic_smooth_inclusion : HolomorphicSmoothInclusionSource (n := n) (M := M)

/-- Native tensor association preserves every actual triple pure tensor. -/
def_wanted native_holomorphic_tensor_associator : TensorAssociatorSource (n := n) (M := M)

/-- The actual tangent-covector wedge induces the normalized native Omega1 tensor Omega1 map. -/
def_wanted native_holomorphic_cotangent_wedge : CotangentWedgeSource (n := n) (M := M)

/-- Actual native smooth coefficient multiplication preserves the same bundle sections. -/
theorem_wanted native_smooth_bundle_section_calculus {r : ℕ} (B : SmoothComplexBundle n M r)
    (A : OneFormValue B) : SectionCalculus B A

/-- Actual native smooth coefficient multiplication preserves the same bundle sections. -/
theorem_wanted native_smooth_bundle_section_multiplication {r : ℕ} (B : SmoothComplexBundle n M r) :
  SmoothSectionMultiplication B

/-- Native smooth bundle section kernels have their ordinary local sheaf condition. -/
theorem_wanted native_smooth_bundle_section_gluing {r : ℕ} (B : SmoothComplexBundle n M r)
    [SectionCalculus B 0] [SmoothSectionMultiplication B] : SmoothBundleSheafCondition B

/-- The actual sheaf Higgs object admits finite holomorphic frames and the same native smooth scalar realization. -/
def_wanted native_holomorphic_higgs_realization [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (T : TensorAssociatorSource (n := n) (M := M)) (W : CotangentWedgeSource (n := n) (M := M))
    (E : HiggsModule T W) : HiggsRealization S E

variable [ExteriorTheory ℝ (Coordinates n) M] [WedgeTheory n M]

/-- Determinant degree data on a compact, connected, Hausdorff, second-countable complex manifold
$M$ modelled on $\mathbb{C}^n$ (smooth as a real manifold), for the inclusion `S` of holomorphic
into smooth complex functions: to every locally free $\mathcal{O}_M$-module $E$ of rank $r$, and to
every finitely presented subsheaf $F$ of such an $E$ of generic rank $q$, it assigns a smooth
complex line bundle realizing the smooth scalar extension of the reflexive determinant
$(\Lambda^r E)^{\vee\vee}$ (resp. $(\Lambda^q F)^{\vee\vee}$), a smooth connection on it and a
closed real $2$-form equal to its first Chern–Weil form (`DeterminantDegreeData`). We assume the
local calculus, gluing and sheafification properties of the functions, sections and forms on $M$
used to define these objects. -/
def_wanted native_determinant_degree_theory [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] (S : HolomorphicSmoothInclusionSource (n := n) (M := M)) : DeterminantDegreeTheory S

/-- The exact harmonic theta and bar-kernel sheaf form the general native Higgs object. -/
def_wanted native_harmonic_kernel_higgs_adapter {r : ℕ} (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A] [KernelSheafCondition B h A]
    (T : TensorAssociatorSource (n := n) (M := M)) (W : CotangentWedgeSource (n := n) (M := M))
    (hh : IsPluriharmonic B h A) (H : HarmonicHiggsModel B h A) : HarmonicKernelHiggsAdapter (T := T) (W := W) B h A H

/-- Every actual harmonic-kernel section maps through the native scalar unit to its original smooth section. -/
def_wanted native_harmonic_kernel_smooth_extension {r : ℕ} (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A] [KernelSheafCondition B h A]
    [SectionCalculus B 0] [SmoothSectionMultiplication B] [SmoothBundleSheafCondition B]
    (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (hh : IsPluriharmonic B h A) : KernelSmoothExtensionSource B h A S

/-- The literal reconstruction from a holomorphic Higgs field satisfies the three actual extraction equations. -/
theorem_wanted native_reconstructed_higgs_pluriharmonic {r : ℕ} (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (H : HolomorphicHiggsField B)
    (C : ConnectionRealization B (reconstructedConnection B h H.value)) : IsPluriharmonic B h C.connection

/-- The inverse comparison preserves the actual theta and the entire same smooth scalar realization. -/
def_wanted native_inverse_higgs_kernel_comparison
    (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (T : TensorAssociatorSource (n := n) (M := M)) (W : CotangentWedgeSource (n := n) (M := M))
    (E : HiggsModule T W) (R : HiggsRealization S E) (h : HermitianMetric R.physical.bundle)
    (C : ConnectionRealization R.physical.bundle
      (reconstructedConnection R.physical.bundle h R.geometry.value))
    [SectionCalculus R.physical.bundle (unitaryPart R.physical.bundle h C.connection)]
    [BarMultiplicationCalculus R.physical.bundle h C.connection]
    [KernelSheafCondition R.physical.bundle h C.connection]
    (H : HarmonicHiggsModel R.physical.bundle h C.connection) : HiggsKernelComparison S E R h C H

/-- Part of the nonabelian Hodge correspondence: let $M$ be a compact, connected, nonempty,
Hausdorff, second-countable complex manifold modelled on $\mathbb{C}^n$ (smooth as a real
manifold) with a Kähler form $\eta$, and let $A$ be a flat connection on a smooth complex vector
bundle $B$ on $M$ whose local system of horizontal sections is semisimple
(`SemisimpleHorizontals`) and which is pluriharmonic for a Hermitian metric $h$
(`IsPluriharmonic`). Then the holomorphic Higgs sheaf of $(B, h, A)$ (`K.object`: the sections
killed by the $(0,1)$-part of the $h$-unitary part of $A$, with the Higgs field of the harmonic
Higgs model `H`) is polystable with respect to $\eta$, slopes being computed from the
determinant degree data `D` and the coordinate integral given by `R` and `P`. We assume the local
calculus, gluing, sheafification and integration properties of the functions, sections and forms
on $M$ used to define these objects. -/
theorem_wanted flat_harmonic_kernel_polystable [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [Nonempty M]
    (S : HolomorphicSmoothInclusionSource (n := n) (M := M)) (D : DeterminantDegreeTheory S)
    (eta : KahlerStructure n M) (R : RealCoordinateMap n) (P : IntegrationAtlas n M)
    [IntegrationTheory n M R P] {r : ℕ} (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B A.value] [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A] [KernelSheafCondition B h A]
    (T : TensorAssociatorSource (n := n) (M := M)) (W : CotangentWedgeSource (n := n) (M := M))
    (hflat : IsFlat B A) (hsemi : SemisimpleHorizontals B A) (hh : IsPluriharmonic B h A)
    (H : HarmonicHiggsModel B h A) (K : HarmonicKernelHiggsAdapter (T := T) (W := W) B h A H) :
  IsPolystable S D eta R P K.object

/-- Part of the nonabelian Hodge correspondence: let $M$ be a compact, connected, nonempty,
Hausdorff, second-countable complex manifold modelled on $\mathbb{C}^n$ (smooth as a real
manifold) with a Kähler form $\eta$, and let $E$ be a locally free holomorphic Higgs sheaf on
$M$ with a smooth realization `F` (a smooth complex vector bundle with a holomorphic Higgs field).
Suppose that $E$ is polystable with respect to $\eta$ (slopes computed from the determinant
degree data `D` and the coordinate integral given by `R` and `P`) and that the rational Chern
classes $c_j$, $j \ge 1$, of the bundle all vanish (`AllRationalChernZero`, for a smooth
connection `C` with the given Chern–Weil forms `A` and singular-cohomology comparison data `I`,
`J`, `Q`, `B`). Then this constructs a Hermitian metric on the bundle that is harmonic for the
Higgs field: the connection reconstructed from the metric and the Higgs field
(`reconstructedConnection`) is flat. We assume the local calculus, gluing, sheafification and
integration properties of the functions, sections and forms on $M$ used to define these objects,
and that smooth singular simplices of $M$ are closed under the simplicial operators. -/
def_wanted polystable_higgs_harmonic_metric [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [Nonempty M] [SmoothSingularSource (n := n) (M := M)]
    (S : HolomorphicSmoothInclusionSource (n := n) (M := M)) (D : DeterminantDegreeTheory S)
    (eta : KahlerStructure n M) (R : RealCoordinateMap n) (P : IntegrationAtlas n M)
    [IntegrationTheory n M R P]
    (T : TensorAssociatorSource (n := n) (M := M)) (W : CotangentWedgeSource (n := n) (M := M))
    (E : HiggsModule T W) (F : HiggsRealization S E)
    (I : SingularIntegrationSource (n := n) (M := M)) (J : RationalCoefficientSource (n := n) (M := M))
    (C : SmoothConnection F.physical.bundle) (A : ∀ q : ℕ, ChernWeilFormSource F.physical.bundle C q)
    (Q : ∀ q : ℕ, EvenDeRhamQuotientSource (n := n) (M := M) q)
    (B : ∀ q : ℕ, RationalChernClassSource F.physical.bundle C I J q (A q) (Q q))
    (hpoly : IsPolystable S D eta R P E)
    (hchern : AllRationalChernZero F.physical.bundle C I J A Q B) :
  {h : HermitianMetric F.physical.bundle // IsHarmonicMetric F.physical.bundle h F.geometry}

/-- Part of the nonabelian Hodge correspondence: let $M$ be a compact, connected, nonempty,
Hausdorff, second-countable complex manifold modelled on $\mathbb{C}^n$ (smooth as a real
manifold) with a Kähler form $\eta$, and let $A$ be a flat connection on a smooth complex vector
bundle $B$ on $M$ that is pluriharmonic for a Hermitian metric $h$ (`IsPluriharmonic`). Then the
local system of horizontal sections of $A$ is semisimple: every locally constant subsheaf of
finite rank of its sheaf of horizontal sections has a retraction. We assume the local calculus,
gluing and sheafification properties of the functions, sections and forms on $M$ used to define
these objects. -/
theorem_wanted pluriharmonic_flat_horizontals_semisimple [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [Nonempty M] (eta : KahlerStructure n M)
    {r : ℕ} (B : SmoothComplexBundle n M r) (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B A.value] [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
    (hflat : IsFlat B A) (hh : IsPluriharmonic B h A) : SemisimpleHorizontals B A

/-- Part of the nonabelian Hodge correspondence: let $M$ be a compact, connected, nonempty,
Hausdorff, second-countable complex manifold modelled on $\mathbb{C}^n$ (smooth as a real
manifold) with a Kähler form $\eta$, let $E$ be a locally free holomorphic Higgs sheaf on $M$
with a smooth realization `R` (a smooth complex vector bundle with a holomorphic Higgs field), and
let $h$, $h'$ be Hermitian metrics on the bundle that are both harmonic for the Higgs field, with
`C`, `C'` realizing the connections reconstructed from them (`reconstructedConnection`). Then
this constructs an automorphism of the Higgs sheaf $E$ (commuting with the Higgs field) whose
smooth scalar extension is a parallel isomorphism from the connection `C` to `C'`
(`HiggsReconstructionIsomorphism`). We assume the local calculus, gluing and sheafification
properties of the functions, sections and forms on $M$ used to define these objects. -/
def_wanted harmonic_higgs_reconstruction_unique [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [Nonempty M] (eta : KahlerStructure n M)
    (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (T : TensorAssociatorSource (n := n) (M := M)) (W : CotangentWedgeSource (n := n) (M := M))
    (E : HiggsModule T W) (R : HiggsRealization S E) (h h' : HermitianMetric R.physical.bundle)
    (C : ConnectionRealization R.physical.bundle
      (reconstructedConnection R.physical.bundle h R.geometry.value))
    (C' : ConnectionRealization R.physical.bundle
      (reconstructedConnection R.physical.bundle h' R.geometry.value))
    (hh : IsHarmonicMetric R.physical.bundle h R.geometry)
    (hh' : IsHarmonicMetric R.physical.bundle h' R.geometry) :
  HiggsReconstructionIsomorphism S E R C.connection C'.connection

/-- Part of the nonabelian Hodge correspondence: let $M$ be a compact, connected, nonempty,
Hausdorff, second-countable complex manifold modelled on $\mathbb{C}^n$ (smooth as a real
manifold) with a Kähler form $\eta$, and let $A$ be a flat connection on a smooth complex vector
bundle $B$ on $M$ whose local system of horizontal sections is semisimple and which is
pluriharmonic for two Hermitian metrics $h$ and $h'$. Then this constructs an isomorphism between
the holomorphic sheaves of $(B, h, A)$ and $(B, h', A)$ (the sections killed by the
$(0,1)$-parts of the unitary parts of $A$) that intertwines the Higgs fields of the harmonic
Higgs models `H` and `H'` and whose smooth scalar extension, through the identifications `I` and
`J` with smooth sections of $B$, is given by an automorphism of $B$ parallel for $A$
(`KernelParallelMapSource`). We assume the local calculus, gluing and sheafification properties
of the functions, sections and forms on $M$ used to define these objects. -/
def_wanted pluriharmonic_metric_higgs_parallel_iso [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [Nonempty M]
    (eta : KahlerStructure n M) {r : ℕ} (B : SmoothComplexBundle n M r) (A : SmoothConnection B)
    [SectionCalculus B A.value] [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
    [SectionCalculus B 0] [SmoothSectionMultiplication B] [SmoothBundleSheafCondition B]
    (h h' : HermitianMetric B)
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A] [KernelSheafCondition B h A]
    [SectionCalculus B (unitaryPart B h' A)] [BarMultiplicationCalculus B h' A] [KernelSheafCondition B h' A]
    (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (I : KernelSmoothExtensionSource B h A S) (J : KernelSmoothExtensionSource B h' A S)
    (hflat : IsFlat B A) (hsemi : SemisimpleHorizontals B A)
    (hh : IsPluriharmonic B h A) (hh' : IsPluriharmonic B h' A)
    (H : HarmonicHiggsModel B h A) (H' : HarmonicHiggsModel B h' A) :
  {e : holomorphicModule B h A ≅ holomorphicModule B h' A //
    e.hom ≫ H'.theta = H.theta ≫ tensorMap e.hom (𝟙 _) ∧
      Nonempty (KernelParallelMapSource B h A S I J e.hom)}
