/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ArithmeticModelHermitianMetrics
public import MathlibExt.AlgebraicGeometry.MetrizedLineOperationModels

/-!
# Native restrictions of full hermitian model metrics

The complexified map is native base change over Spec Z. Line comparisons
are the native pullback-composition comparisons. Their fibre maps and
norms use the actual residue-field comorphism and every pulled-back
local section.

Compatibility with an adelic model is tested on every model local
section at every archimedean place and every isometric embedding of its
completed residue field into C. Such an embedding determines the complex
model point by the literal scheme map, rather than a selected point map.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 1.1.3 and 3.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HermitianModelRestrictions

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open ArithmeticModelHermitianMetrics PlacewiseMetrizedLineModels
open AdelicArithmeticModelFrames ComplexAnalytification

def complexMap {Y Z : Scheme.{0}} (f : Y ⟶ Z) : complexScheme Y ⟶ complexScheme Z :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom ℂ)))).map
    (show Over.mk (integerMap Y) ⟶ Over.mk (integerMap Z) from
      Over.homMk f (specZIsTerminal.hom_ext _ _))

theorem complexMap_projection {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    (complexMap f).left ≫ complexProjection Z = complexProjection Y ≫ f := by
  simp [complexMap, complexProjection, Over.pullback]

def complexPullbackLine {Y Z : Scheme.{0}} (f : Y ⟶ Z) (L : Z.Modules) :
    (Scheme.Modules.pullback (complexMap f).left).obj (complexLine L) ≅
      complexLine ((Scheme.Modules.pullback f).obj L) :=
  (Scheme.Modules.pullbackComp (complexMap f).left (complexProjection Z)).app L ≪≫
    eqToIso (congrArg (fun g ↦ (Scheme.Modules.pullback g).obj L)
      (complexMap_projection f)) ≪≫
    ((Scheme.Modules.pullbackComp (complexProjection Y) f).app L).symm

/-- The restriction is on the actual pullback line, with full native fibre norms. -/
structure HermitianPullback {Y Z : Scheme.{0}} (f : Y ⟶ Z) {L : Z.Modules}
    (H : HermitianLine L) where
  hermitian : HermitianLine ((Scheme.Modules.pullback f).obj L)
  fibre : MetrizedLineOperationModels.PullbackFibre ℂ (complexScheme Z) (complexLine L)
    (complexMap f)
  pullback : MetrizedLineOperationModels.PullbackMetric ℂ (complexScheme Z) (complexLine L)
    (complexMap f) fibre H.metric
  lineFibre : MetrizedLineOperationModels.FibreIso ℂ (complexScheme Y)
    ((Scheme.Modules.pullback (complexMap f).left).obj (complexLine L))
    (complexLine ((Scheme.Modules.pullback f).obj L)) (complexPullbackLine f L)
  normalized : ∀ p z,
    (hermitian.metric.fibreNorm p).norm (lineFibre.map p z) =
      (pullback.metric.fibreNorm p).norm z

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} (M : ArithmeticModel A X L)

def IsArchimedean (v : A.places) : Prop :=
  ¬ ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖

/-- Standard archimedean normalization is retained on the actual completed place field. -/
structure StandardArchimedeanPlace (v : A.places) where
  embedding : A.completion v →+* ℂ
  isometry : ∀ a, ‖embedding a‖ = ‖a‖

/-- An actual isometric embedding of the original point's completed residue field. -/
structure ComplexPointExtension (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)) where
  embedding : ValuedLineFibres.CompletedResidue (A.completion v) (placeScheme A X v) p →+* ℂ
  isometry : ∀ a, ‖embedding a‖ = ‖a‖

/-- Actual standard places and extensions make every archimedean point comparison nonvacuous. -/
structure ArchimedeanPoints where
  place : ∀ (v : A.places), IsArchimedean v → StandardArchimedeanPlace (A := A) v
  extension : ∀ (v : A.places) (_hv : IsArchimedean v)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)), ComplexPointExtension v p
  normalized : ∀ (v : A.places) (hv : IsArchimedean v)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)) (a : A.completion v),
    (extension v hv p).embedding (ValuedLineFibres.completionUnit _ _ p
      (BerkovichAnalytification.scalarMap _ _ p.schemePoint a)) = (place v hv).embedding a

def ComplexPointExtension.modelMap {v : A.places}
    {p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)}
    (E : ComplexPointExtension v p) : Spec (.of ℂ) ⟶ M.scheme :=
  Spec.map (CommRingCat.ofHom (E.embedding.comp (ValuedLineFibres.completionUnit _ _ p))) ≫
    (placeScheme A X v).left.fromSpecResidueField p.schemePoint ≫ placeModelMap M v

def ComplexPointExtension.modelPoint {v : A.places}
    {p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)}
    (E : ComplexPointExtension v p) : ComplexPoints (complexScheme M.scheme).hom :=
  ⟨pullback.lift (E.modelMap M) (𝟙 (Spec (.of ℂ))) (specZIsTerminal.hom_ext _ _), by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simp⟩

theorem ComplexPointExtension.modelPoint_projection {v : A.places}
    {p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)}
    (E : ComplexPointExtension v p) :
    (E.modelPoint M).hom ≫ complexProjection M.scheme = E.modelMap M := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  simp

/-- Every original model open has exactly the same membership at the complex realization. -/
theorem ComplexPointExtension.modelPoint_mem {v : A.places}
    {p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)}
    (E : ComplexPointExtension v p) (U : M.scheme.Opens) :
    (E.modelPoint M).Mem (complexProjection M.scheme ⁻¹ᵁ U) ↔
      placeModelMap M v p.schemePoint ∈ U := by
  rw [ComplexPoints.mem_iff (IsLocalRing.closedPoint ℂ)]
  change ((E.modelPoint M).hom ≫ complexProjection M.scheme) (IsLocalRing.closedPoint ℂ) ∈ U ↔ _
  rw [E.modelPoint_projection M]
  change (placeModelMap M v)
    ((placeScheme A X v).left.fromSpecResidueField p.schemePoint
      ((Spec.map (CommRingCat.ofHom (E.embedding.comp
        (ValuedLineFibres.completionUnit _ _ p)))) (IsLocalRing.closedPoint ℂ))) ∈ U ↔ _
  rw [Scheme.fromSpecResidueField_apply]

/-- The full model hermitian metric determines the given archimedean model norms. -/
def IsModelMetric (H : HermitianLine M.line) (N : MetrizedLine A X L) : Prop :=
  ∀ (v : A.places), IsArchimedean v →
    ∀ (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
      (E : ComplexPointExtension v p) (U : M.scheme.Opens) (s : Γ(M.line,U))
      (hp : placeModelMap M v p.schemePoint ∈ U)
      (hq : (E.modelPoint M).Mem (complexProjection M.scheme ⁻¹ᵁ U)),
      norm N v p (ValuedLineFibres.evaluateSection _ _ _ (pullModelSection M v s) p hp) =
        (H.metric.fibreNorm (H.dictionary.point (E.modelPoint M))).norm
          (ValuedLineFibres.evaluateSection _ _ _ (complexSection U s)
            (H.dictionary.point (E.modelPoint M)) (by
              change (E.modelPoint M).schemePoint ∈ _
              exact (ComplexPoints.schemePoint_mem_iff _ _).mpr hq))

end MathlibExt.AlgebraicGeometry.HermitianModelRestrictions
