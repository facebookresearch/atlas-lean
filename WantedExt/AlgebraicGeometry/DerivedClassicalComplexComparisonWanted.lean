/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps
public import MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack
public import MathlibExt.AlgebraicGeometry.DerivedNativeComplexTruncation
public import MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonClassicalCoefficientFamilyUnit
public import MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonClassicalIdentitySourceTransportEquivalence

/-!
# Wanted native classical comparison for the universally glueable DG moduli locus

Every source construction below has fixed coefficient, sheaf, interval,
adjunction or localization maps in its public contract. The actual
groupoid comparison, its equivalence, scalar naturality and coherent
composition assertions are separate results; the coherent unit assertion
`classical_coefficient_family_unit` is proved in
`MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonClassicalCoefficientFamilyUnit`.
No equivalence is asserted for unrestricted ordinary-coefficient M_k or
for a general T-action after forgetting that action.

References: Toën--Vaquié math/0503269v5 §3.1 pp36--37 and p8;
Stacks 03G8, 06YY, 0D6D, 0DLD/0DLE. The native ordinary-stack source
is ComplexesStack.lean at AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b; its general algebraic-space
algebraicity theorem is not re-requested here.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels
open MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
open MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps
open MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack
open MathlibExt.AlgebraicGeometry.DerivedNativeComplexTruncation
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

universe u

/-- For every scheme $X$, the presheaf of rings on the small étale site of $X$ that sends an étale
$X$-scheme $U$ to its ring of global sections $\Gamma(U, \mathcal{O}_U)$
(`etaleStructurePresheaf`) is a sheaf for the étale topology (`EtaleStructureSource`). -/
theorem_wanted classical_etale_structure_source (X : Scheme.{u}) : EtaleStructureSource X

/-- Assemble actual ringed inverse images and their native total left derivations. -/
def_wanted classical_etale_pullback_system
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) : EtalePullbackSystem O

/-- Construct the actual Zar-to-étale module source with all test restrictions normalized. -/
def_wanted classical_affine_etale_module_source
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (A : CommRingCat.{u}) :
  AffineEtaleModuleSource O A

/-- Adapt the native pullback-pasting comparisons, fixing their action on every test section. -/
def_wanted classical_etale_pushforward_coherence
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O) :
  EtalePushforwardCoherence L

/-- The displayed native counit composite is a total left derivation of the actual composite pullback. -/
theorem_wanted classical_etale_composite_derivation
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (C : EtalePushforwardCoherence L) (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) :
  EtaleCompositeDerivationSource C f g

/-- Normalize N(const A) by its actual Moore coefficient projection in every degree. -/
def_wanted classical_ordinary_coefficient_source (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (A : CommAlgCat.{u} k) : OrdinaryCoefficientSource N A

/-- Extract actual A-module cochains and every homogeneous component from the full DG module action. -/
def_wanted classical_ordinary_module_source (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (A : CommAlgCat.{u} k) (C : OrdinaryCoefficientSource N A) :
  OrdinaryModuleSource C

/-- Choose an actual point of the scalar-category Reedy frame. -/
def_wanted classical_scalar_frame_point (k : Type u) [CommRing k]
    (R : DGFrame k (oppositeCategory (scalarCategory k))) : ScalarFramePoint R

/-- Construct the actual closed interval arrow whose scalar augmentation is the identity. -/
def_wanted classical_scalar_frame_interval (k : Type u) [CommRing k]
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R) :
  ScalarFrameInterval r

/-- Transport only the native endpoint equalities of every edge's actual interval image. -/
def_wanted classical_scalar_frame_edge_maps (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (I : ScalarFrameInterval r) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k) :
  ScalarFrameEdgeMaps I P A

/-- Assemble the prescribed ordinary/sheaf realizations and preservation of the actual field-Ext locus. -/
def_wanted classical_ordinary_complex_source_system (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) : OrdinaryComplexSourceSystem r P O L

/-- Native scheme tilde pullback agrees with actual coefficient extension on 1 tensor x. -/
def_wanted classical_tilde_affine_pullback_source (A B : CommRingCat.{u}) (f : A ⟶ B) :
  TildeAffinePullbackSource f

/-- Construct the coefficient maps with their actual module unit and all-test étale adjunction mates. -/
def_wanted classical_coefficient_map_system (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (Z : OrdinaryComplexSourceSystem r P O L) :
  CoefficientMapSystem Z

/-- The source field-Ext condition is preserved by this actual derived inverse image. -/
theorem_wanted classical_pullback_preserves_source
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A B : CommRingCat.{u}) (f : A ⟶ B)
    (J : AffineEtaleModuleSource O A) (J' : AffineEtaleModuleSource O B) :
  ClassicalPullbackSource L f J J'

/-- A native coefficient-perfect vertex yields an actual bounded projective affine presentation. -/
theorem_wanted classical_vertex_is_affine_perfect (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    (C : OrdinaryCoefficientSource N A) (V : OrdinaryModuleSource C)
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (J : AffineEtaleModuleSource O (ordinaryRing A))
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
  IsAffinePerfect J (vertexEtaleDerived r P A V J E)

/-- Construct the classical groupoid comparison, fixing every actual vertex and edge image. -/
def_wanted classical_complex_groupoid_comparison (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (I : ScalarFrameInterval r) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    (F : ScalarFrameEdgeMaps I P A) (C : OrdinaryCoefficientSource N A) (V : OrdinaryModuleSource C)
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) : ClassicalComplexComparison F V L J

/-- Equivalence is a theorem about the actual constructed functor on the correct restricted locus. -/
theorem_wanted classical_complex_groupoid_comparison_equivalence (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (I : ScalarFrameInterval r) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    (F : ScalarFrameEdgeMaps I P A) (C : OrdinaryCoefficientSource N A) (V : OrdinaryModuleSource C)
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) (G : ClassicalComplexComparison F V L J) :
  G.functor.IsEquivalence

/-- The displayed scalar comparison is an isomorphism; its source map is already fixed independently. -/
theorem_wanted classical_coefficient_family_map_isIso (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (Z : OrdinaryComplexSourceSystem r P O L) (D : CoefficientMapSystem Z)
    (A B : CommAlgCat.{u} k) (f : A ⟶ B) (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
  IsIso (coefficientFamilyMap D f E)

/-- Composite coefficients give the exact native derived composition mate and the two actual unit maps. -/
theorem_wanted classical_coefficient_family_composition (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (Z : OrdinaryComplexSourceSystem r P O L) (D : CoefficientMapSystem Z)
    (C : EtalePushforwardCoherence L) (A B C' : CommAlgCat.{u} k) (f : A ⟶ B) (g : B ⟶ C')
    (H : EtaleCompositeDerivationSource C
      (Spec.map (CommRingCat.ofHom g.hom.toRingHom))
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom)))
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
  HEq (coefficientFamilyMap D (f ≫ g) E)
    ((etaleDerivedComp H).hom.app
      (vertexEtaleDerived r P A (Z.module A) (Z.etale A) E) ≫
      (etaleDerivedPullback (L.derived (Spec.map (CommRingCat.ofHom g.hom.toRingHom)))).map
        (coefficientFamilyMap D f E) ≫
      coefficientFamilyMap D g (((underivedModuliFunctor R P).map f).app (op ⦋0⦌) E))

/-- Scalar naturality is constructed with every component equal to the same literal derived map. -/
def_wanted classical_complex_comparison_coefficient_naturality (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (I : ScalarFrameInterval r) (P : StrictPerfectSystem N S)
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (Z : OrdinaryComplexSourceSystem r P O L) (D : CoefficientMapSystem Z)
    (A B : CommAlgCat.{u} k) (f : A ⟶ B) (F : ScalarFrameEdgeMaps I P A) (F' : ScalarFrameEdgeMaps I P B)
    (G : ClassicalComplexComparison F (Z.module A) L (Z.etale A))
    (G' : ClassicalComplexComparison F' (Z.module B) L (Z.etale B))
    (H : ClassicalPullbackSource L (CommRingCat.ofHom f.hom.toRingHom) (Z.etale A) (Z.etale B)) :
  ClassicalCoefficientNaturality Z f G G' H (D.tilde f) (D.ordinary f) (D.etale f)

/-- Adapt the actual source projection, including every literal X_y to X_A field comparison. -/
theorem_wanted classical_identity_source_transport (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A : CommAlgCat.{u} k) (J : AffineEtaleModuleSource O (ordinaryRing A)) :
  IdentityComplexesTransportSource L A J

/-- The final truncation comparison is to the literal native perfect/no-negative-fibre-Ext X_A groupoid. -/
theorem_wanted classical_native_identity_moduli_comparison_equivalence (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (I : ScalarFrameInterval r) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    (F : ScalarFrameEdgeMaps I P A) (C : OrdinaryCoefficientSource N A) (V : OrdinaryModuleSource C)
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) (G : ClassicalComplexComparison F V L J)
    (H : IdentityComplexesTransportSource L A J) :
  (nativeIdentityModuliComparison G H).IsEquivalence

/-- The ordinary source locus has no higher automorphism homotopy, for this literal nerve comparison. -/
theorem_wanted classical_native_identity_ordinary_space_comparison (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (I : ScalarFrameInterval r) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    (F : ScalarFrameEdgeMaps I P A) (C : OrdinaryCoefficientSource N A) (V : OrdinaryModuleSource C)
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) (G : ClassicalComplexComparison F V L J)
    (H : IdentityComplexesTransportSource L A J) :
  WeakEquivalence (nativeOrdinaryComplexComparison G H)
