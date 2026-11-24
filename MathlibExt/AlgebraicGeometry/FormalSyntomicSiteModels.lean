/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticSyntomicModels
public import MathlibExt.AlgebraicGeometry.FormalProObjectSites
public import MathlibExt.AlgebraicGeometry.FiniteTateCoefficientTowers
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.CategoryTheory.FunctorialKInjective

/-!
# Syntomic restriction on the actual formal étale site

The source base is the actual norm-unit ring O_C with its fixed Z_p map.
Every affine formal open retains a p-complete quasisyntomic ring and its
literal Spf diagram on all nilpotent levels. A quasisyntomic sheaf is
restricted by the limit over *all* such affine opens, as in BMS Remark
10.4. All actual chart maps fix the restriction, so no affine-zero test
or freely named formal syntomic complex defines the comparison.

The finite source is cone(p^r) on these actual restricted syntomic
cochains. Its modulus map is the native cone map of the square whose
source is multiplication by p and whose target is the identity.

Reference: BMS19 arXiv:1802.03261v2, Section 7.4, Theorem 10.1,
Remarks 10.3/10.4 and Theorem 1.15(2).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FormalSyntomicSiteModels

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open FormalGenericFibreModels FormalNearbyCycleModels
open PrismaticSyntomicModels AbsolutePrismaticBasis PrismaticFilteredTwists

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (C : CompletePadicField p)

/-- The actual O_C qsyn model; its Z_p coefficients are the original
inclusion into the given complete extension of Q_p. -/
structure IntegralBase where
  ring : QuasiSyntomicPrismSites.Ring p
  iso : ring.algebra ≃+* integers p C
  coefficient : ∀ a : PadicInt p,
    ((iso (algebraMap (PadicInt p) ring.algebra a) : integers p C) : C.carrier) =
      algebraMap ℚ_[p] C.carrier (a : ℚ_[p])

variable (B : IntegralBase p C)

abbrev QsynSite := (QuasiSyntomicPrismSites.Relative p B.ring)ᵒᵖ
abbrev QsynSheaves := Sheaf (QuasiSyntomicPrismSites.topology p B.ring) (ModuleCat.{1} ℤ)

def basisInclusion : (AbsolutePrismaticBasis.Basis p B.ring)ᵒᵖ ⥤ QsynSite p C B :=
  (ObjectProperty.ι _).op

variable [(basisInclusion p C B).IsContinuous (AbsolutePrismaticBasis.topology p B.ring)
  (QuasiSyntomicPrismSites.topology p B.ring)]

def basisRestriction : QsynSheaves p C B ⥤ PrismaticNygaardCohomology.Sheaves p B.ring :=
  (basisInclusion p C B).sheafPushforwardContinuous (ModuleCat.{1} ℤ)
    (AbsolutePrismaticBasis.topology p B.ring) (QuasiSyntomicPrismSites.topology p B.ring)

instance basisRestriction_additive : (basisRestriction p C B).Additive where
  map_add := by intros; rfl

variable
  (D : ∀ S : AbsolutePrismaticBasis.Basis p B.ring, InitialLift p (AbsolutePrismaticBasis.ring p S))
  (Z : ZeroReduction p B.ring D) (T : TwistTower p B.ring D Z)
  (F : FrobeniusModel p B.ring D Z T)

/-- Source extension from the actual semiperfectoid basis, constructed
with its entire cochain and restriction dictionary. -/
structure QsynExtension where
  complex : ∀ i : ℤ, CochainComplex (QsynSheaves p C B) ℤ
  basis : ∀ i : ℤ,
    ((basisRestriction p C B).mapHomologicalComplex (.up ℤ)).obj (complex i) ≅ F.syntomic i

variable {D Z T F}
  (X : FormalGenericFibreModels.FormalScheme p C)

/-- A native affine formal open with its actual qsyn coefficient ring. -/
structure AffineChart (U : FormalEtaleSite p C X) where
  ring : QuasiSyntomicPrismSites.Relative p B.ring
  formal : FormalGenericFibreModels.FormalScheme p C
  iso : PadicFormalSchemes.spfDiagram p ring.obj.right.algebra ⊥ ≅ formal.diagram
  base : iso.hom ≫ formal.structureMap =
    PadicFormalSchemes.mapDiagram p
      (ring.obj.hom.toRingHom.comp B.iso.symm.toRingHom) (I := ⊥) (J := ⊥) (by simp)
  inclusion : formal ⟶ U.obj.left
  [openCharts : ∀ n, IsOpenImmersion ((PadicFormalSchemes.FormalScheme.Hom.diagram inclusion).app n)]

attribute [instance] AffineChart.openCharts

variable {X} {U V W : FormalEtaleSite p C X}

/-- All chart maps retain their original ring map and every nilpotent map. -/
@[ext] structure ChartMap (f : U ⟶ V) (A : AffineChart p C B X U) (E : AffineChart p C B X V) where
  ring : E.ring ⟶ A.ring
  formal : A.formal ⟶ E.formal
  normalized : PadicFormalSchemes.FormalScheme.Hom.diagram formal =
    A.iso.inv ≫ PadicFormalSchemes.mapDiagram p ring.hom.right.toRingHom
      (I := ⊥) (J := ⊥) (by simp) ≫ E.iso.hom
  square : A.inclusion ≫ f.hom.left = formal ≫ E.inclusion

namespace ChartMap

variable {p C B}

def identity (A : AffineChart p C B X U) : ChartMap p C B (𝟙 U) A A where
  ring := 𝟙 A.ring
  formal := 𝟙 A.formal
  normalized := by
    change 𝟙 A.formal.diagram = A.iso.inv ≫
      PadicFormalSchemes.mapDiagram p (RingHom.id _) (I := ⊥) (J := ⊥) (by simp) ≫ A.iso.hom
    simp
  square := by simp

def comp {f : U ⟶ V} {g : V ⟶ W}
    {A : AffineChart p C B X U} {E : AffineChart p C B X V} {H : AffineChart p C B X W}
    (a : ChartMap p C B f A E) (b : ChartMap p C B g E H) : ChartMap p C B (f ≫ g) A H where
  ring := b.ring ≫ a.ring
  formal := a.formal ≫ b.formal
  normalized := by
    change PadicFormalSchemes.FormalScheme.Hom.diagram a.formal ≫
      PadicFormalSchemes.FormalScheme.Hom.diagram b.formal = _
    rw [a.normalized, b.normalized]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc
      (PadicFormalSchemes.mapDiagram p a.ring.hom.right.toRingHom (I := ⊥) (J := ⊥) (by simp))
      (PadicFormalSchemes.mapDiagram p b.ring.hom.right.toRingHom (I := ⊥) (J := ⊥) (by simp))
      H.iso.hom, PadicFormalSchemes.mapDiagram_comp]
    rfl
  square := by
    change A.inclusion ≫ (f.hom.left ≫ g.hom.left) = (a.formal ≫ b.formal) ≫ H.inclusion
    rw [← Category.assoc, a.square, Category.assoc, b.square, Category.assoc]

end ChartMap

namespace AffineChart

variable {p C B}

instance : Category (AffineChart p C B X U) where
  Hom A E := ChartMap p C B (𝟙 U) A E
  id A := ChartMap.identity A
  comp a b :=
    { ring := b.ring ≫ a.ring
      formal := a.formal ≫ b.formal
      normalized := (ChartMap.comp a b).normalized
      square := by simpa [ChartMap.comp] using (ChartMap.comp a b).square }
  id_comp a := by apply ChartMap.ext <;> simp [ChartMap.identity]
  comp_id a := by apply ChartMap.ext <;> simp [ChartMap.identity]
  assoc a b c := by apply ChartMap.ext <;> simp [Category.assoc]

def toQsyn (U : FormalEtaleSite p C X) : AffineChart p C B X U ⥤ QsynSite p C B where
  obj A := op A.ring
  map a := a.ring.op
  map_id _ := rfl
  map_comp _ _ := rfl

end AffineChart

variable (X)

instance affineModuleLimits (U : FormalEtaleSite p C X) :
    HasLimitsOfShape (AffineChart p C B X U)ᵒᵖ (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfShape

/-- The source's literal limit over all actual affine opens Spf(R) ⊂ U. -/
def affineSections (U : FormalEtaleSite p C X) : QsynSheaves p C B ⥤ ModuleCat.{1} ℤ :=
  sheafToPresheaf (QuasiSyntomicPrismSites.topology p B.ring) _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (AffineChart.toQsyn (p := p) (C := C) (B := B) U).op ⋙
      lim.{0, 1, 1, 2}

/-- Formal restriction is fixed by the source's affine-limit formula and
by every actual square over every formal étale arrow. -/
structure FormalRestriction where
  functor : QsynSheaves p C B ⥤ FormalSheaves p C X
  [additive : functor.Additive]
  affine : ∀ U : FormalEtaleSite p C X,
    functor ⋙ sheafToPresheaf (formalEtaleTopology p C X) _ ⋙
      (evaluation (FormalEtaleSite p C X)ᵒᵖ (ModuleCat.{1} ℤ)).obj (op U) ≅ affineSections p C B X U
  normalized : ∀ {U V : FormalEtaleSite p C X} (f : U ⟶ V)
    (A : AffineChart p C B X U) (E : AffineChart p C B X V) (a : ChartMap p C B f A E)
    (M : QsynSheaves p C B),
    (functor.obj M).obj.map f.op ≫ (affine U).hom.app M ≫
      limit.π ((AffineChart.toQsyn (p := p) (C := C) (B := B) U).op ⋙ M.obj) (op A) =
    (affine V).hom.app M ≫
      limit.π ((AffineChart.toQsyn (p := p) (C := C) (B := B) V).op ⋙ M.obj) (op E) ≫
        M.obj.map a.ring.op.op

attribute [instance] FormalRestriction.additive

namespace FormalRestriction

variable {p C B X} (R : FormalRestriction p C B X)
  (Q : QsynExtension p C B D Z T F) (RQ : FunctorialKInjective (QsynSheaves p C B))

/-- The derived formal restriction of the syntomic cochains: the restriction functor applied to a
K-injective resolution of the extended complex, which computes its right derived functor
(Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral p-adic Hodge theory*,
Thm. 10.1 and Rem. 10.4, use descent for complexes). Applying the restriction termwise to the
short extended complex itself would lose all higher quasisyntomic cohomology. -/
def syntomic (i : ℤ) : CochainComplex (FormalSheaves p C X) ℤ :=
  (R.functor.mapHomologicalComplex (.up ℤ)).obj (RQ.functor.obj (Q.complex i))

/-- Every coefficient level is a derived p-power cone on the same source. -/
def finite (i : ℤ) (r : ℕ) : CochainComplex (FormalSheaves p C X) ℤ :=
  CochainComplex.mappingCone ((p ^ (r + 1) : ℤ) • (𝟙 (R.syntomic Q RQ i)))

/-- The actual coefficient-reduction square: p on the source, 1 on target. -/
def reduction (i : ℤ) (r : ℕ) : R.finite Q RQ i (r + 1) ⟶ R.finite Q RQ i r :=
  HomologicalComplex.homotopyCofiber.mapArrowHom
    ((p ^ (r + 2) : ℤ) • (𝟙 (R.syntomic Q RQ i)))
    ((p ^ (r + 1) : ℤ) • (𝟙 (R.syntomic Q RQ i)))
    (fun j : ℤ ↦ ⟨j - 1, by simp⟩)
    (Arrow.homMk ((p : ℤ) • (𝟙 (R.syntomic Q RQ i))) (𝟙 _) (by
      change ((p : ℤ) • (𝟙 (R.syntomic Q RQ i))) ≫
        ((p ^ (r + 1) : ℤ) • (𝟙 (R.syntomic Q RQ i))) =
          ((p ^ (r + 2) : ℤ) • (𝟙 (R.syntomic Q RQ i))) ≫ 𝟙 _
      simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
        Category.comp_id, smul_smul]
      rw [← pow_succ]))

end FormalRestriction

end MathlibExt.AlgebraicGeometry.FormalSyntomicSiteModels
