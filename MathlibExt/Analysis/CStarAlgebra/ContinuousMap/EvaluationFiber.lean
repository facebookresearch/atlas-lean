/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.Hom
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.CanonicalBaseChange
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.GradedLeft
public import MathlibExt.Analysis.CStarAlgebra.Grading.Module.Self
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.ContinuousMap
import Mathlib.Tactic.FinCases

/-!
# Canonical maps into coefficient-change tensors and evaluation fibres

The original complete module is arbitrary. Coefficient change uses the
actual balanced radical quotient and its completion. For nonunital target
coefficients the canonical vector map is constructed from the existing
strict right-factorization theorem and is characterized by the genuine
approximate-unit limit `pure(x,u)`. No coefficient unit is introduced.

All inner products, right actions and norms are the original ones. The
evaluation fibre is not restricted to a continuous-function module on a
fixed vector carrier. No Source theorem, supplied output grading, endpoint
unitary, substitute norm or relation/group is used by this module.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped CStarAlgebra CStarModule.Right RightActions


namespace CStarModule.ContinuousMap.EvaluationFiber

universe uΩ uB uE

variable {Ω : Type uΩ} [TopologicalSpace Ω] [CompactSpace Ω]
variable {B : Type uB} [NonUnitalCStarAlgebra B]

/-- Mathlib's spectral order on an opposite coefficient algebra, used locally
for the evaluation tensor and its coefficient self-module. -/
local instance oppositeSpectralOrder (A : Type*) [NonUnitalCStarAlgebra A] :
    PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ

/-- The star-order laws for the local opposite spectral-order dictionary. -/
local instance oppositeSpectralOrderedRing (A : Type*) [NonUnitalCStarAlgebra A] :
    StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul (C(Ω, B))ᵐᵒᵖ E] [CStarModule (C(Ω, B))ᵐᵒᵖ E] [CompleteSpace E]

open CStarModule.InternalTensorProduct

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `t ∈ Ω`. Point evaluation acts on the coefficient self-module `B`.

The evaluation followed by the coefficient self-module action. -/
def coefficientAction (t : Ω) :
    C(Ω, B) →⋆ₙₐ[ℂ] AdjointableOperator.End B B :=
  (AdjointableOperator.leftRegular (B := B)).comp
    (_root_.ContinuousMap.evalNonUnitalStarAlgHom (A := B) t)

omit [CompactSpace Ω] in
/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `t ∈ Ω`. Point evaluation acts on the coefficient self-module `B`.

Evaluation acts on the coefficient algebra by multiplication. -/
@[simp]
theorem coefficientAction_apply (t : Ω) (f : C(Ω, B)) (b : B) :
    coefficientAction (B := B) t f b = f t * b := by
  rfl

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `t ∈ Ω`. Point evaluation acts on the coefficient self-module `B`.

The evaluated coefficient action really takes values in module compacts. -/
def coefficientCompactAction (t : Ω) :
    C(Ω, B) →⋆ₙₐ[ℂ] AdjointableOperator.CompactEnd B B :=
  (AdjointableOperator.leftRegularCompact (B := B)).comp
    (_root_.ContinuousMap.evalNonUnitalStarAlgHom (A := B) t)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The fibre is the completed balanced evaluation tensor of E. -/
abbrev Carrier (t : Ω) :=
  CompletedTensor (E₁ := E) (coefficientAction (B := B) t)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The completed evaluation fibre carries the quotient/completion norm of the balanced tensor
product. -/
@[instance_reducible]
def normedAddCommGroup (t : Ω) : NormedAddCommGroup (Carrier (B := B) (E := E) t) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedAddCommGroup (coefficientAction (B := B) t)
  exact inferInstance

attribute [local instance] CStarModule.ContinuousMap.EvaluationFiber.normedAddCommGroup

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The completed evaluation fibre is a normed complex vector space for that norm. -/
@[instance_reducible]
def normedSpace (t : Ω) : NormedSpace ℂ (Carrier (B := B) (E := E) t) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedAddCommGroup (coefficientAction (B := B) t)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedSpace (coefficientAction (B := B) t)
  exact inferInstance

attribute [local instance] CStarModule.ContinuousMap.EvaluationFiber.normedSpace

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The completed evaluation fibre carries its natural right action of `B`. -/
@[instance_reducible]
def rightAction (t : Ω) : SMul Bᵐᵒᵖ (Carrier (B := B) (E := E) t) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedAddCommGroup (coefficientAction (B := B) t)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedSpace (coefficientAction (B := B) t)
  letI : SMul Bᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalRightAction (coefficientAction (B := B) t)
  exact inferInstance

attribute [local instance] CStarModule.ContinuousMap.EvaluationFiber.rightAction

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The evaluation fibre is a normed right C*-module over `B`, with the balanced tensor inner
product. -/
@[instance_reducible]
def cstarModule (t : Ω) : CStarModule Bᵐᵒᵖ (Carrier (B := B) (E := E) t) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedAddCommGroup (coefficientAction (B := B) t)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedSpace (coefficientAction (B := B) t)
  letI : SMul Bᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalRightAction (coefficientAction (B := B) t)
  exact completedCStarModule (coefficientAction (B := B) t)

attribute [local instance] CStarModule.ContinuousMap.EvaluationFiber.cstarModule

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The pure map uses the two quotients and completion inclusion. -/
def pure (t : Ω) (x : E) (b : B) : Carrier (B := B) (E := E) t := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedAddCommGroup (coefficientAction (B := B) t)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedSpace (coefficientAction (B := B) t)
  exact completedPure (coefficientAction (B := B) t) x b

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The completed evaluation tensor has the internal tensor-product universal structure for the
source module and the evaluated coefficient self-module. -/
theorem isModel (t : Ω) : IsModel (coefficientAction (B := B) t) (pure (B := B) (E := E) t) := by
  let _ : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedAddCommGroup (coefficientAction (B := B) t)
  let _ : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalTensorNormedSpace (coefficientAction (B := B) t)
  let _ : SMul Bᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction (B := B) t)) :=
    radicalRightAction (coefficientAction (B := B) t)
  exact completed_isModel (coefficientAction (B := B) t)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The canonical vector evaluation into an arbitrary completed module fibre. -/
def evaluation (t : Ω) : E →L[ℂ] Carrier (B := B) (E := E) t :=
  IsModel.canonicalBaseChangeMap (isModel (B := B) (E := E) t)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

inner products evaluate literally at the chosen point. -/
@[simp]
theorem evaluation_inner (t : Ω) (x y : E) :
    CStarModule.rightInner (B := B) (evaluation (B := B) (E := E) t x) (evaluation (B := B) (E := E) t y) =
      (CStarModule.rightInner (B := C(Ω, B)) x y) t :=
  IsModel.canonicalBaseChangeMap_inner (isModel (B := B) (E := E) t) x y

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The canonical evaluation is contractive in the module norm. -/
theorem norm_evaluation_le (t : Ω) (x : E) : ‖evaluation (B := B) (E := E) t x‖ ≤ ‖x‖ :=
  IsModel.norm_canonicalBaseChangeMap_le (isModel (B := B) (E := E) t) x

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The kernel is exactly the null space of the evaluated inner square. -/
theorem evaluation_eq_zero_iff (t : Ω) (x : E) :
    evaluation (B := B) (E := E) t x = 0 ↔ (CStarModule.rightInner (B := C(Ω, B)) x x) t = 0 := by
  rw [← evaluation_inner t x x]
  constructor
  · intro h
    rw [h, CStarModule.rightInner_zero_right]
  · intro h
    apply (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp
    apply MulOpposite.unop_injective
    simpa only [CStarModule.rightInner, MulOpposite.unop_zero] using h

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

Right coefficients change by the point evaluation. -/
@[simp]
theorem evaluation_right_smul (t : Ω) (x : E) (f : C(Ω, B)) :
    evaluation (B := B) (E := E) t (x <• f) = evaluation (B := B) (E := E) t x <• f t :=
  IsModel.canonicalBaseChangeMap_right_smul (isModel (B := B) (E := E) t) x f

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

Pure tensors are right multiples of the evaluated vector. -/
theorem evaluation_pure (t : Ω) (x : E) (b : B) :
    evaluation (B := B) (E := E) t x <• b = pure (B := B) (E := E) t x b :=
  IsModel.canonicalBaseChangeMap_pure (isModel (B := B) (E := E) t) x b

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

Point evaluation is surjective on the coefficient algebra, so the canonical vector image is
dense in the completed fibre. -/
theorem evaluation_denseRange (t : Ω) : DenseRange (evaluation (B := B) (E := E) t) := by
  apply IsModel.canonicalBaseChangeMap_denseRange_of_surjective (isModel (B := B) (E := E) t)
  intro b
  exact ⟨_root_.ContinuousMap.const Ω b, rfl⟩

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

Adjointable endomorphisms descend through the balanced completion. -/
def endomorphismMap (t : Ω) :
    AdjointableOperator.End C(Ω, B) E →⋆ₐ[ℂ]
      AdjointableOperator.End B (Carrier (B := B) (E := E) t) :=
  IsModel.mapLeftStarAlgHom (isModel (B := B) (E := E) t)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The descended operator has the action on every canonical image. -/
@[simp]
theorem endomorphismMap_evaluation (t : Ω)
    (T : AdjointableOperator.End C(Ω, B) E) (x : E) :
    endomorphismMap (B := B) (E := E) t T (evaluation (B := B) (E := E) t x) = evaluation (B := B) (E := E) t (T x) :=
  IsModel.mapLeftStarAlgHom_canonicalBaseChangeMap (isModel (B := B) (E := E) t) T x

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The same computed operator retains every pure-tensor value. -/
@[simp]
theorem endomorphismMap_pure (t : Ω)
    (T : AdjointableOperator.End C(Ω, B) E) (x : E) (b : B) :
    endomorphismMap (B := B) (E := E) t T (pure (B := B) (E := E) t x b) = pure (B := B) (E := E) t (T x) b :=
  IsModel.mapLeftStarAlgHom_pure (isModel (B := B) (E := E) t) T x b

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

Module compacts descend through the coefficient self-action. -/
def compactMap (t : Ω) :
    AdjointableOperator.CompactEnd C(Ω, B) E →⋆ₙₐ[ℂ]
      AdjointableOperator.CompactEnd B (Carrier (B := B) (E := E) t) :=
  IsModel.baseChangeCompactHom (isModel (B := B) (E := E) t)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`.

The rank-one image pins the compact map to the vectors. -/
@[simp]
theorem compactMap_rankOne (t : Ω) (x y : E) :
    (compactMap (B := B) (E := E) t ⟨AdjointableOperator.rankOne (B := C(Ω, B)) x y,
      AdjointableOperator.rankOne_mem_compact x y⟩ :
        AdjointableOperator.End B (Carrier (B := B) (E := E) t)) =
      AdjointableOperator.rankOne (B := B) (evaluation (B := B) (E := E) t x) (evaluation (B := B) (E := E) t y) :=
  IsModel.mapLeftStarAlgHom_rankOne_baseChange (isModel (B := B) (E := E) t) x y

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`. Assume that `E` is countably generated as a module over
`C(Ω,B)`.

The evaluation fibre is countably generated as a right module over `B`. -/
theorem countablyGenerated (t : Ω)
    (hE : CStarModule.IsCountablyGenerated (B := C(Ω, B)) (E := E)) :
    CStarModule.IsCountablyGenerated (B := B) (E := Carrier (B := B) (E := E) t) :=
  IsModel.countablyGenerated_baseChange (isModel (B := B) (E := E) t) hE

/-! ## Computed coefficient and endpoint gradings -/

/-- Let `B` be a possibly nonunital complex C*-algebra with a specified C*-grading. Its right
coefficient self-module carries the induced grading.

The left coefficient action is graded for the computed self-module. -/
def gradedLeftRegular (γ : CStarGrading B) :
    CStarGrading.Hom γ (CStarModuleGrading.self γ).operatorGrading where
  toNonUnitalStarAlgHom := AdjointableOperator.leftRegular (B := B)
  equivariant' := by
    intro n b
    change AdjointableOperator.leftRegular
        (PointNormCStarAddAction.aut γ n.toAdd b) =
      PointNormCStarAddAction.aut (CStarModuleGrading.self γ).operatorGrading n.toAdd
        (AdjointableOperator.leftRegular b)
    have hn (k : ZMod 2) : k = 0 ∨ k = 1 := by
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hn n.toAdd with h0 | h1
    · rw [h0]
      simp only [PointNormCStarAddAction.aut_zero, StarAlgEquiv.one_apply]
    · rw [h1]
      change AdjointableOperator.leftRegular (γ.generatorAut b) =
        (CStarModuleGrading.self γ).operatorGrading.generatorAut
          (AdjointableOperator.leftRegular b)
      rw [CStarModuleGrading.operatorGrading_generatorAut]
      apply AdjointableOperator.ext
      intro x
      rw [CStarModuleGrading.operatorGenerator_apply]
      simp only [CStarModuleGrading.self_generator_apply,
        AdjointableOperator.leftRegular_apply]
      rw [map_mul, γ.generator_apply_generator]

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `t ∈ Ω`. Point evaluation acts on the coefficient self-module `B`. A specified C*-grading of
`B` is retained.

Point evaluation composed with the graded coefficient self-action. -/
def gradedCoefficientAction (γ : CStarGrading B) (t : Ω) :
    CStarGrading.Hom (PointNormCStarAction.continuousMap Ω γ)
      (CStarModuleGrading.self γ).operatorGrading :=
  CStarGrading.Hom.comp (gradedLeftRegular γ)
    (PointNormCStarAction.continuousMapEvaluation γ t)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `t ∈ Ω`. Point evaluation acts on the coefficient self-module `B`. A specified C*-grading of
`B` is retained.

The graded representation has exactly the same ordinary evaluation action. -/
@[simp]
theorem gradedCoefficientAction_toNonUnitalStarAlgHom
    (γ : CStarGrading B) (t : Ω) :
    (gradedCoefficientAction γ t).toNonUnitalStarAlgHom = coefficientAction (B := B) t := by
  rfl

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`. Specify a C*-grading on `B` and a compatible grading on
`E`.

The evaluation fibre carries the grading induced by the specified source and coefficient
gradings. -/
def grading (γ : CStarGrading B)
    (δ : CStarModuleGrading (PointNormCStarAction.continuousMap Ω γ) E)
    (t : Ω) : CStarModuleGrading γ (Carrier (B := B) (E := E) t) :=
  CStarModule.InternalTensorProduct.Grading.modelGrading δ (CStarModuleGrading.self γ)
    (gradedCoefficientAction γ t) (pure (B := B) (E := E) t) (isModel (B := B) (E := E) t)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`. Specify a C*-grading on `B` and a compatible grading on
`E`.

Every pure vector has the unsigned factor-generator formula. -/
@[simp]
theorem grading_generator_pure (γ : CStarGrading B)
    (δ : CStarModuleGrading (PointNormCStarAction.continuousMap Ω γ) E)
    (t : Ω) (x : E) (b : B) :
    (grading γ δ t).generator (pure (B := B) (E := E) t x b) =
      pure (B := B) (E := E) t (δ.generator x) (γ.generatorAut b) := by
  have hp :=
    CStarModule.InternalTensorProduct.Grading.modelGrading_generator_pure
      (B₁ := C(Ω, B)) (B₂ := B) (E₁ := E) (E₂ := B)
      (X := Carrier (B := B) (E := E) t)
      (γ₁ := PointNormCStarAction.continuousMap Ω γ) (γ₂ := γ)
      δ (CStarModuleGrading.self γ) (gradedCoefficientAction γ t)
      (pure (B := B) (E := E) t) (isModel (B := B) (E := E) t) x b
  change (grading γ δ t).generator (pure (B := B) (E := E) t x b) =
    pure (B := B) (E := E) t (δ.generator x)
      ((CStarModuleGrading.self γ).generator b) at hp
  rw [CStarModuleGrading.self_generator_apply] at hp
  exact hp

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`. Specify a C*-grading on `B` and a compatible grading on
`E`.

The canonical vector evaluation intertwines the module gradings. -/
@[simp]
theorem grading_evaluation (γ : CStarGrading B)
    (δ : CStarModuleGrading (PointNormCStarAction.continuousMap Ω γ) E)
    (t : Ω) (x : E) :
    (grading γ δ t).generator (evaluation (B := B) (E := E) t x) = evaluation (B := B) (E := E) t (δ.generator x) := by
  obtain ⟨y, a, h⟩ :=
    CStarModule.exists_right_factor_of_starOrderedRing (B := C(Ω, B)) (E := E) x
  have hx : evaluation (B := B) (E := E) t x = pure (B := B) (E := E) t y (a t) :=
    IsModel.canonicalBaseChangeMap_factor (isModel (B := B) (E := E) t) x y a h
  have hδx : δ.generator x = δ.generator y <•
      CStarGrading.generatorAut (PointNormCStarAction.continuousMap Ω γ) a := by
    rw [h, δ.generator_right_smul]
  rw [hx, grading_generator_pure]
  symm
  calc
    evaluation (B := B) (E := E) t (δ.generator x) = pure (B := B) (E := E) t (δ.generator y)
        ((CStarGrading.generatorAut (PointNormCStarAction.continuousMap Ω γ) a) t) :=
      IsModel.canonicalBaseChangeMap_factor (isModel (B := B) (E := E) t)
        (δ.generator x) (δ.generator y)
        (CStarGrading.generatorAut (PointNormCStarAction.continuousMap Ω γ) a) hδx
    _ = pure (B := B) (E := E) t (δ.generator y) (γ.generatorAut (a t)) := by
      simp only [CStarGrading.generatorAut_apply, PointNormCStarAction.continuousMap_apply]

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`. Specify a C*-grading on `B` and a compatible grading on
`E`.

Graded adjointable source endomorphisms induce graded adjointable endomorphisms of the
evaluation fibre. -/
def gradedEndomorphismMap (γ : CStarGrading B)
    (δ : CStarModuleGrading (PointNormCStarAction.continuousMap Ω γ) E)
    (t : Ω) :
    CStarGrading.Hom δ.operatorGrading (grading γ δ t).operatorGrading :=
  IsModel.gradedLeftHom (isModel (B := B) (E := E) t)
    δ (CStarModuleGrading.self γ) (grading γ δ t)
    (fun x b => by
      simpa only [CStarModuleGrading.self_generator_apply] using
        grading_generator_pure γ δ t x b)

/-- Let `Ω` be a compact topological space, let `B` be a possibly nonunital complex C*-algebra, and
let `E` be a complete normed right C*-module over `C(Ω,B)`, with its compatible complex
normed-space structure. Fix `t ∈ Ω`. Specify a C*-grading on `B` and a compatible grading on
`E`.

Forgetting the grading recovers the same computed ordinary End map. -/
@[simp]
theorem gradedEndomorphismMap_toNonUnitalStarAlgHom (γ : CStarGrading B)
    (δ : CStarModuleGrading (PointNormCStarAction.continuousMap Ω γ) E)
    (t : Ω) :
    (gradedEndomorphismMap γ δ t).toNonUnitalStarAlgHom =
      (endomorphismMap (B := B) (E := E) t).toNonUnitalStarAlgHom :=
  rfl

end CStarModule.ContinuousMap.EvaluationFiber
