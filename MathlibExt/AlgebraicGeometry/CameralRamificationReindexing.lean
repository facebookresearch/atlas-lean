/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralFoundationPackages
public import MathlibExt.AlgebraicGeometry.RelativeLambdaReindexing

/-!
# Cross-cover ramification symbol, dual and section normalization

Arrows are actual Cartesian maps of the finite cameral schemes. The
symbol comparison is fixed on every native affine coefficient generator
through the actual tilde presentations. Its computed-dual comparison is
fixed by the perfect internal-Hom evaluation pairing. Evaluation into O
may have a kernel, and does not replace the symbol module.

Identity, composition and every coefficient map retain the native
pullback comparisons. This supplies normalization on arbitrary nonreduced
pullbacks of the universal Chevalley cover, including empty unramified loci.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5.2--5.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralRamificationReindexing

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CameralFoundationPackages CameralTorusBands CameralIncidenceModels
open CameralRamificationSymbols CameralSymbolReindexModels
open CoherentCurveLinearSeries NativeLineDuals LineBundleTaskContracts
open RelativeLambdaReindexing FiniteCoverLocalComparison

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, ExpansionParameterModels.TorusTheory ℂ n} (F : Foundation G tori)

abbrev Cover (X : Over (Spec (.of ℂ))) :=
  CameralCover F.Weyl F.chevalley.chevalley X

def total {X : Over (Spec (.of ℂ))} (C : Cover F X) : Over (Spec (.of ℂ)) := overScheme C.cover

def projection {X : Over (Spec (.of ℂ))} (C : Cover F X) : total F C ⟶ X :=
  coverProjection C.cover

def reflection {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    (total F C).left ≅ (total F C).left := schemeCoverIso C.cover (F.roots.reflection i)

def ideal {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    IdealSymbols (total F C) (reflection F C i) := (F.ramification X C i).1

def presentation {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    GlobalPresentation (ideal F C i) := (F.ramification X C i).2.1

def sectionData {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    RamificationSection (ideal F C i) := (F.ramification X C i).2.2.1

def line {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    (total F C).left.Modules := ramificationLine (ideal F C i)

def frames {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    TorusLineFrameModels.LineFrames (tori 1) (total F C) (line F C i) :=
  (F.ramification X C i).2.2.2

/-- The perfect pairing with the computed sheaf dual, rather than ideal evaluation. -/
def dualEvaluation {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    AlgebraicLineBundleFamilies.moduleTensor (total F C).left (ideal F C i).module (line F C i) ⟶
      structureModule (total F C).left :=
  tensorMap (𝟙 (ideal F C i).module)
    (eqToIso (sectionData F C i).duality.object_eq).inv ≫
      (sectionData F C i).duality.evaluation.evaluation

/-- A map of cameral covers over a map of bases: a Cartesian square that commutes with the
Weyl group actions on both covers (Donagi–Gaitsgory, Defs. 2.5–2.6). -/
structure CameralArrow {X X' : Over (Spec (.of ℂ))} (C : Cover F X) (C' : Cover F X') where
  base : X ⟶ X'
  total : total F C ⟶ total F C'
  projection : total ≫ projection F C' = projection F C ≫ base
  cartesian : IsPullback total.left C.cover.scheme.hom C'.cover.scheme.hom base.left
  weyl : ∀ w : F.Weyl,
    (schemeCoverIso C.cover w).hom ≫ total.left = total.left ≫ (schemeCoverIso C'.cover w).hom

def ReflectionCompatible {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (i j : Fin F.roots.count) : Prop :=
  (reflection F C i).hom ≫ m.total.left = m.total.left ≫ (reflection F C' j).hom

/-- A map of cameral covers commutes with each simple reflection. -/
theorem CameralArrow.reflectionCompatible {X X' : Over (Spec (.of ℂ))} {C : Cover F X}
    {C' : Cover F X'} (m : CameralArrow F C C') (i : Fin F.roots.count) :
    ReflectionCompatible F m i i :=
  m.weyl (F.roots.reflection i)

structure RootChartArrow {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') {i j : Fin F.roots.count}
    (U : AffineReflection (total F C) (reflection F C i))
    (V : AffineReflection (total F C') (reflection F C' j)) where
  coefficients : V.algebra →ₐ[ℂ] U.algebra
  symbols : CoefficientMap (s := V.reflection) (s' := U.reflection) coefficients
  sheaf : SheafMap coefficients symbols
  geometric : Spec.map (CommRingCat.ofHom coefficients.toRingHom) ≫
    V.chart.hom ≫ V.neighborhood.val.ι = U.chart.hom ≫ U.neighborhood.val.ι ≫ m.total.left

structure SymbolPullback {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (i j : Fin F.roots.count) (_h : ReflectionCompatible F m i j) where
  comparison : (Scheme.Modules.pullback m.total.left).obj (ideal F C' j).module ≅
    (ideal F C i).module
  chartCover : ∀ y : (total F C).left,
    ∃ (U : AffineReflection (total F C) (reflection F C i))
      (V : AffineReflection (total F C') (reflection F C' j)),
      y ∈ U.neighborhood.val ∧ Nonempty (RootChartArrow F m U V)
  coefficients : ∀ (U : AffineReflection (total F C) (reflection F C i))
      (V : AffineReflection (total F C') (reflection F C' j)) (a : RootChartArrow F m U V),
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom a.coefficients.toRingHom))).map
      ((presentation F C' j).presentation V).hom ≫ a.sheaf.map =
    (Scheme.Modules.pullbackComp
      (Spec.map (CommRingCat.ofHom a.coefficients.toRingHom))
      (V.chart.hom ≫ V.neighborhood.val.ι)).hom.app (ideal F C' j).module ≫
      (Scheme.Modules.pullbackCongr (by simpa only [Category.assoc] using a.geometric)).hom.app
        (ideal F C' j).module ≫
      (Scheme.Modules.pullbackComp (U.chart.hom ≫ U.neighborhood.val.ι) m.total.left).inv.app
        (ideal F C' j).module ≫
      (Scheme.Modules.pullback (U.chart.hom ≫ U.neighborhood.val.ι)).map comparison.hom ≫
        ((presentation F C i).presentation U).hom
  evaluation : (Scheme.Modules.pullback m.total.left).map (ideal F C' j).evaluation ≫
      (pullbackStructureIso m.total.left).hom = comparison.hom ≫ (ideal F C i).evaluation

structure RamificationPullback {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (i j : Fin F.roots.count) (h : ReflectionCompatible F m i j) where
  symbols : SymbolPullback F m i j h
  tensor : TensorPullbackComparison m.total.left
  line : (Scheme.Modules.pullback m.total.left).obj (line F C' j) ≅ line F C i
  pairing : (Scheme.Modules.pullback m.total.left).map (dualEvaluation F C' j) ≫
      (pullbackStructureIso m.total.left).hom =
    (tensor.iso (ideal F C' j).module (CameralRamificationReindexing.line F C' j)).hom ≫
      tensorMap symbols.comparison.hom line.hom ≫ dualEvaluation F C i
  sectionMap : pullbackSection m.total.left (sectionData F C' j).sectionMap ≫ line.hom =
    (sectionData F C i).sectionMap

structure RamificationReindexing where
  map : ∀ {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (i j : Fin F.roots.count) (h : ReflectionCompatible F m i j),
    RamificationPullback F m i j h
  unit : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (m : CameralArrow F C C)
      (hm : m.total = 𝟙 (total F C)) (i : Fin F.roots.count) (h : ReflectionCompatible F m i i),
    (map m i i h).symbols.comparison.hom =
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hm)).hom.app (ideal F C i).module ≫
        (Scheme.Modules.pullbackId (total F C).left).hom.app (ideal F C i).module
  composition : ∀ {X₀ X₁ X₂ : Over (Spec (.of ℂ))}
      {C₀ : Cover F X₀} {C₁ : Cover F X₁} {C₂ : Cover F X₂}
      (m₀₁ : CameralArrow F C₀ C₁) (m₁₂ : CameralArrow F C₁ C₂) (m₀₂ : CameralArrow F C₀ C₂)
      (hm : m₀₂.total = m₀₁.total ≫ m₁₂.total) (i j k : Fin F.roots.count)
      (h₀₁ : ReflectionCompatible F m₀₁ i j) (h₁₂ : ReflectionCompatible F m₁₂ j k)
      (h₀₂ : ReflectionCompatible F m₀₂ i k),
    (map m₀₂ i k h₀₂).symbols.comparison.hom =
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hm)).hom.app (ideal F C₂ k).module ≫
        (Scheme.Modules.pullbackComp m₀₁.total.left m₁₂.total.left).inv.app (ideal F C₂ k).module ≫
        (Scheme.Modules.pullback m₀₁.total.left).map (map m₁₂ j k h₁₂).symbols.comparison.hom ≫
        (map m₀₁ i j h₀₁).symbols.comparison.hom
  dual_unit : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (m : CameralArrow F C C)
      (hm : m.total = 𝟙 (total F C)) (i : Fin F.roots.count) (h : ReflectionCompatible F m i i),
    (map m i i h).line.hom =
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hm)).hom.app (line F C i) ≫
        (Scheme.Modules.pullbackId (total F C).left).hom.app (line F C i)
  dual_composition : ∀ {X₀ X₁ X₂ : Over (Spec (.of ℂ))}
      {C₀ : Cover F X₀} {C₁ : Cover F X₁} {C₂ : Cover F X₂}
      (m₀₁ : CameralArrow F C₀ C₁) (m₁₂ : CameralArrow F C₁ C₂) (m₀₂ : CameralArrow F C₀ C₂)
      (hm : m₀₂.total = m₀₁.total ≫ m₁₂.total) (i j k : Fin F.roots.count)
      (h₀₁ : ReflectionCompatible F m₀₁ i j) (h₁₂ : ReflectionCompatible F m₁₂ j k)
      (h₀₂ : ReflectionCompatible F m₀₂ i k),
    (map m₀₂ i k h₀₂).line.hom =
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hm)).hom.app (line F C₂ k) ≫
        (Scheme.Modules.pullbackComp m₀₁.total.left m₁₂.total.left).inv.app (line F C₂ k) ≫
        (Scheme.Modules.pullback m₀₁.total.left).map (map m₁₂ j k h₁₂).line.hom ≫
        (map m₀₁ i j h₀₁).line.hom

structure CameralBaseChange {X X' : Over (Spec (.of ℂ))} (C : Cover F X) (f : X' ⟶ X) where
  cover : Cover F X'
  comparison : total F cover ≅ CameralTorusBands.pulled F.Weyl C.cover (Over.mk f.left)
  projection : comparison.hom.left ≫ pullback.snd C.cover.scheme.hom f.left = cover.cover.scheme.hom
  action : ∀ w,
    (schemeCoverIso cover.cover w).hom ≫ comparison.hom.left =
      comparison.hom.left ≫ (CameralTorusBands.pulledAction F.Weyl C.cover (Over.mk f.left) w).hom
  arrow : CameralArrow F cover C
  base : arrow.base = f
  original : arrow.total.left = comparison.hom.left ≫ pullback.fst C.cover.scheme.hom f.left

end MathlibExt.AlgebraicGeometry.CameralRamificationReindexing
