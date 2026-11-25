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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Creation
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Generation
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.ModelComparison.Left
public import MathlibExt.Analysis.CStarAlgebra.Module.Factorization
public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Canonical nonunital coefficient change and compact transport

An arbitrary complete right Hilbert module changes coefficients through an
actual balanced tensor model. The canonical vector map uses strict right
factorization and is characterized by its approximate-unit limit. The
operator map preserves genuine rank-one operators and module compacts.

The public definitions and proofs are relocated unchanged from the former
generic block in `ContinuousMap.EvaluationFiber`. This core has no point
evaluation, continuous-map, or grading dependency.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped CStarAlgebra CStarModule.Right RightActions

namespace CStarModule.InternalTensorProduct.IsModel

universe uA uB uE uF

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder Aᵐᵒᵖ] [StarOrderedRing Aᵐᵒᵖ]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] [CompleteSpace E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
variable {g : A →⋆ₙₐ[ℂ] B} {pure : E → B → F}

/-- Mathlib's spectral order on the target coefficient algebra, used locally
to construct its increasing approximate unit. -/
local instance coefficientSpectralOrder : PartialOrder B :=
  CStarAlgebra.spectralOrder B

/-- The star-order laws for the local target-coefficient spectral order. -/
local instance coefficientSpectralOrderedRing : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

local instance coefficientApproximateUnitNeBot :
    NeBot (CStarAlgebra.approximateUnit B) :=
  (CStarAlgebra.increasingApproximateUnit (A := B)).toIsApproximateUnit.neBot

private theorem exists_factorPair (x : E) :
    ∃ p : E × A, x = p.1 <• p.2 := by
  obtain ⟨y, a, h⟩ :=
    CStarModule.exists_right_factor_of_starOrderedRing (B := A) (E := E) x
  exact ⟨(y, a), h⟩

private def factorPair (x : E) : E × A :=
  Classical.choose (exists_factorPair (A := A) x)

private theorem factorPair_spec (x : E) :
    x = (factorPair (A := A) x).1 <• (factorPair (A := A) x).2 :=
  Classical.choose_spec (exists_factorPair (A := A) x)

private def canonicalFunction (g : A →⋆ₙₐ[ℂ] B)
    (pure : E → B → F) (x : E) : F :=
  pure (factorPair (A := A) x).1 (g (factorPair (A := A) x).2)

private theorem canonicalFunction_tendsto
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x : E) :
    Tendsto (fun u : B => pure x u) (CStarAlgebra.approximateUnit B)
      (𝓝 (canonicalFunction g pure x)) := by
  let p : E × A := factorPair (A := A) x
  let T := creationOnModel
    ((AdjointableOperator.leftRegular (B := B)).comp g) pure hF p.1
  have hu : Tendsto (fun u : B => g p.2 * u)
      (CStarAlgebra.approximateUnit B) (𝓝 (g p.2)) :=
    (CStarAlgebra.increasingApproximateUnit (A := B)).tendsto_mul_left (g p.2)
  have ht : Tendsto (fun u : B => pure p.1 (g p.2 * u))
      (CStarAlgebra.approximateUnit B) (𝓝 (canonicalFunction g pure x)) := by
    have hT := T.toContinuousLinearMap.continuous.continuousAt.tendsto.comp hu
    change Tendsto (fun u : B => T (g p.2 * u))
      (CStarAlgebra.approximateUnit B) (𝓝 (T (g p.2))) at hT
    simpa only [T, creationOnModel_apply, canonicalFunction, p] using hT
  refine ht.congr' (Eventually.of_forall fun u => ?_)
  symm
  rw [factorPair_spec (A := A) x]
  simpa only [NonUnitalStarAlgHom.comp_apply,
    AdjointableOperator.leftRegular_apply, p] using
    hF.2.2.2.2.1 (factorPair (A := A) x).1 (factorPair (A := A) x).2 u

private theorem canonicalFunction_factor
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x y : E) (a : A) (h : x = y <• a) :
    canonicalFunction g pure x = pure y (g a) := by
  let T := creationOnModel
    ((AdjointableOperator.leftRegular (B := B)).comp g) pure hF y
  have hu : Tendsto (fun u : B => g a * u)
      (CStarAlgebra.approximateUnit B) (𝓝 (g a)) :=
    (CStarAlgebra.increasingApproximateUnit (A := B)).tendsto_mul_left (g a)
  have ht : Tendsto (fun u : B => pure y (g a * u))
      (CStarAlgebra.approximateUnit B) (𝓝 (pure y (g a))) := by
    have hT := T.toContinuousLinearMap.continuous.continuousAt.tendsto.comp hu
    change Tendsto (fun u : B => T (g a * u))
      (CStarAlgebra.approximateUnit B) (𝓝 (T (g a))) at hT
    simpa only [T, creationOnModel_apply] using hT
  have hx : Tendsto (fun u : B => pure x u)
      (CStarAlgebra.approximateUnit B) (𝓝 (pure y (g a))) := by
    refine ht.congr' (Eventually.of_forall fun u => ?_)
    symm
    rw [h]
    simpa only [NonUnitalStarAlgHom.comp_apply,
      AdjointableOperator.leftRegular_apply] using hF.2.2.2.2.1 y a u
  exact tendsto_nhds_unique (canonicalFunction_tendsto hF x) hx

private theorem canonicalFunction_inner
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x y : E) :
    CStarModule.rightInner (B := B)
        (canonicalFunction g pure x) (canonicalFunction g pure y) =
      g (CStarModule.rightInner (B := A) x y) := by
  let px : E × A := factorPair (A := A) x
  let py : E × A := factorPair (A := A) y
  have hx : x = px.1 <• px.2 := factorPair_spec (A := A) x
  have hy : y = py.1 <• py.2 := factorPair_spec (A := A) y
  have hinner : CStarModule.rightInner (B := A) x y =
      star px.2 * CStarModule.rightInner (B := A) px.1 py.1 * py.2 := by
    rw [hx, hy, CStarModule.rightInner_left_smul,
      CStarModule.rightInner_right_smul]
    exact (mul_assoc _ _ _).symm
  change CStarModule.rightInner (B := B)
      (pure px.1 (g px.2)) (pure py.1 (g py.2)) = _
  rw [hF.2.2.2.2.2.2.1, hinner, map_mul, map_mul, map_star]
  simp only [NonUnitalStarAlgHom.comp_apply,
    AdjointableOperator.leftRegular_apply, CStarModule.Right.rightInner_self]
  exact (mul_assoc _ _ _).symm

private theorem canonicalFunction_norm_le
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x : E) : ‖canonicalFunction g pure x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg x)).mp
  calc
    ‖canonicalFunction g pure x‖ ^ 2 =
        ‖CStarModule.rightInner (B := B)
          (canonicalFunction g pure x) (canonicalFunction g pure x)‖ :=
      (CStarModule.norm_rightInner_self (B := B) _).symm
    _ = ‖g (CStarModule.rightInner (B := A) x x)‖ := by
      rw [canonicalFunction_inner hF]
    _ ≤ ‖CStarModule.rightInner (B := A) x x‖ :=
      NonUnitalStarAlgHom.norm_apply_le g _
    _ = ‖x‖ ^ 2 := CStarModule.norm_rightInner_self (B := A) x

private theorem canonicalFunction_add
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x y : E) :
    canonicalFunction g pure (x + y) =
      canonicalFunction g pure x + canonicalFunction g pure y := by
  have ht : Tendsto (fun u : B => pure (x + y) u)
      (CStarAlgebra.approximateUnit B)
      (𝓝 (canonicalFunction g pure x + canonicalFunction g pure y)) := by
    refine ((canonicalFunction_tendsto hF x).add
      (canonicalFunction_tendsto hF y)).congr' ?_
    exact Eventually.of_forall fun u => (hF.1 x y u).symm
  exact tendsto_nhds_unique (canonicalFunction_tendsto hF (x + y)) ht

private theorem canonicalFunction_smul
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (c : ℂ) (x : E) :
    canonicalFunction g pure (c • x) = c • canonicalFunction g pure x := by
  have ht : Tendsto (fun u : B => pure (c • x) u)
      (CStarAlgebra.approximateUnit B) (𝓝 (c • canonicalFunction g pure x)) := by
    refine ((canonicalFunction_tendsto hF x).const_smul c).congr' ?_
    exact Eventually.of_forall fun u => (hF.2.2.1 c x u).symm
  exact tendsto_nhds_unique (canonicalFunction_tendsto hF (c • x)) ht

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

Coefficient change along g defines a canonical contractive complex-linear map from E to F.
-/
def canonicalBaseChangeMap
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure) :
    E →L[ℂ] F := by
  have hfactor (x : E) : ∃ p : E × A, x = p.1 <• p.2 := by
    obtain ⟨y, a, h⟩ :=
      CStarModule.exists_right_factor_of_starOrderedRing (B := A) (E := E) x
    exact ⟨(y, a), h⟩
  let factor : E → E × A := fun x => Classical.choose (hfactor x)
  have hfactor_spec (x : E) : x = (factor x).1 <• (factor x).2 :=
    Classical.choose_spec (hfactor x)
  let value : E → F := fun x => pure (factor x).1 (g (factor x).2)
  have hvalue_tendsto (x : E) :
      Tendsto (fun u : B => pure x u) (CStarAlgebra.approximateUnit B)
        (𝓝 (value x)) := by
    let p : E × A := factor x
    let T := creationOnModel
      ((AdjointableOperator.leftRegular (B := B)).comp g) pure hF p.1
    have hu : Tendsto (fun u : B => g p.2 * u)
        (CStarAlgebra.approximateUnit B) (𝓝 (g p.2)) :=
      (CStarAlgebra.increasingApproximateUnit (A := B)).tendsto_mul_left (g p.2)
    have ht : Tendsto (fun u : B => pure p.1 (g p.2 * u))
        (CStarAlgebra.approximateUnit B) (𝓝 (value x)) := by
      have hT := T.toContinuousLinearMap.continuous.continuousAt.tendsto.comp hu
      change Tendsto (fun u : B => T (g p.2 * u))
        (CStarAlgebra.approximateUnit B) (𝓝 (T (g p.2))) at hT
      simpa only [T, creationOnModel_apply, value, p] using hT
    refine ht.congr' (Eventually.of_forall fun u => ?_)
    symm
    rw [hfactor_spec x]
    simpa only [NonUnitalStarAlgHom.comp_apply,
      AdjointableOperator.leftRegular_apply, p] using
      hF.2.2.2.2.1 (factor x).1 (factor x).2 u
  have hvalue_inner (x y : E) :
      CStarModule.rightInner (B := B) (value x) (value y) =
        g (CStarModule.rightInner (B := A) x y) := by
    let px : E × A := factor x
    let py : E × A := factor y
    have hx : x = px.1 <• px.2 := hfactor_spec x
    have hy : y = py.1 <• py.2 := hfactor_spec y
    have hinner : CStarModule.rightInner (B := A) x y =
        star px.2 * CStarModule.rightInner (B := A) px.1 py.1 * py.2 := by
      rw [hx, hy, CStarModule.rightInner_left_smul,
        CStarModule.rightInner_right_smul]
      exact (mul_assoc _ _ _).symm
    change CStarModule.rightInner (B := B)
        (pure px.1 (g px.2)) (pure py.1 (g py.2)) = _
    rw [hF.2.2.2.2.2.2.1, hinner, map_mul, map_mul, map_star]
    simp only [NonUnitalStarAlgHom.comp_apply,
      AdjointableOperator.leftRegular_apply, CStarModule.Right.rightInner_self]
    exact (mul_assoc _ _ _).symm
  have hvalue_norm (x : E) : ‖value x‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg x)).mp
    calc
      ‖value x‖ ^ 2 =
          ‖CStarModule.rightInner (B := B) (value x) (value x)‖ :=
        (CStarModule.norm_rightInner_self (B := B) _).symm
      _ = ‖g (CStarModule.rightInner (B := A) x x)‖ := by rw [hvalue_inner]
      _ ≤ ‖CStarModule.rightInner (B := A) x x‖ :=
        NonUnitalStarAlgHom.norm_apply_le g _
      _ = ‖x‖ ^ 2 := CStarModule.norm_rightInner_self (B := A) x
  have hvalue_add (x y : E) : value (x + y) = value x + value y := by
    have ht : Tendsto (fun u : B => pure (x + y) u)
        (CStarAlgebra.approximateUnit B) (𝓝 (value x + value y)) := by
      refine ((hvalue_tendsto x).add (hvalue_tendsto y)).congr' ?_
      exact Eventually.of_forall fun u => (hF.1 x y u).symm
    exact tendsto_nhds_unique (hvalue_tendsto (x + y)) ht
  have hvalue_smul (c : ℂ) (x : E) : value (c • x) = c • value x := by
    have ht : Tendsto (fun u : B => pure (c • x) u)
        (CStarAlgebra.approximateUnit B) (𝓝 (c • value x)) := by
      refine ((hvalue_tendsto x).const_smul c).congr' ?_
      exact Eventually.of_forall fun u => (hF.2.2.1 c x u).symm
    exact tendsto_nhds_unique (hvalue_tendsto (c • x)) ht
  let L : E →ₗ[ℂ] F :=
    { toFun := value
      map_add' := hvalue_add
      map_smul' := hvalue_smul }
  exact L.mkContinuous 1 fun x => by
    change ‖value x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using hvalue_norm x

private theorem canonicalBaseChangeMap_apply
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x : E) : canonicalBaseChangeMap hF x = canonicalFunction g pure x := by
  simp only [canonicalBaseChangeMap, LinearMap.mkContinuous_apply,
    canonicalFunction, factorPair]
  rfl

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

For x ∈ E, the pure vectors pure(x,u) converge to the canonical image of x as u tends along the
approximate unit of B.
-/
theorem canonicalBaseChangeMap_tendsto
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x : E) :
    Tendsto (fun u : B => pure x u) (CStarAlgebra.approximateUnit B)
      (𝓝 (canonicalBaseChangeMap hF x)) := by
  rw [canonicalBaseChangeMap_apply]
  exact canonicalFunction_tendsto hF x

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

If x = ya for x, y ∈ E and a ∈ A, the canonical image of x is pure(y,g(a)).
-/
theorem canonicalBaseChangeMap_factor
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x y : E) (a : A) (h : x = y <• a) :
    canonicalBaseChangeMap hF x = pure y (g a) := by
  rw [canonicalBaseChangeMap_apply]
  exact canonicalFunction_factor hF x y a h

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

The canonical vector map changes inner products by g: ⟨j(x),j(y)⟩ = g(⟨x,y⟩) for x, y ∈ E.
-/
@[simp]
theorem canonicalBaseChangeMap_inner
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x y : E) :
    CStarModule.rightInner (B := B)
        (canonicalBaseChangeMap hF x) (canonicalBaseChangeMap hF y) =
      g (CStarModule.rightInner (B := A) x y) := by
  rw [canonicalBaseChangeMap_apply, canonicalBaseChangeMap_apply]
  exact canonicalFunction_inner hF x y

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

For x ∈ E, the canonical vector map satisfies ‖j(x)‖ ≤ ‖x‖.
-/
theorem norm_canonicalBaseChangeMap_le
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x : E) : ‖canonicalBaseChangeMap hF x‖ ≤ ‖x‖ := by
  rw [canonicalBaseChangeMap_apply]
  exact canonicalFunction_norm_le hF x

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

For x ∈ E and a ∈ A, the canonical vector map satisfies j(xa) = j(x)g(a).
-/
@[simp]
theorem canonicalBaseChangeMap_right_smul
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x : E) (a : A) :
    canonicalBaseChangeMap hF (x <• a) = canonicalBaseChangeMap hF x <• g a :=
  CStarModule.map_right_smul_of_map_rightInner g
    (canonicalBaseChangeMap hF) (canonicalBaseChangeMap_inner hF) x a

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

For x ∈ E and b ∈ B, the pure vector pure(x,b) equals j(x)b.
-/
theorem canonicalBaseChangeMap_pure
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x : E) (b : B) : canonicalBaseChangeMap hF x <• b = pure x b := by
  have hleft : Tendsto (fun u : B => pure x u <• b)
      (CStarAlgebra.approximateUnit B) (𝓝 (canonicalBaseChangeMap hF x <• b)) :=
    (CStarModule.continuous_right_smul_const b).continuousAt.tendsto.comp
      (canonicalBaseChangeMap_tendsto hF x)
  let T := creationOnModel
    ((AdjointableOperator.leftRegular (B := B)).comp g) pure hF x
  have hu : Tendsto (fun u : B => u * b)
      (CStarAlgebra.approximateUnit B) (𝓝 b) :=
    (CStarAlgebra.increasingApproximateUnit (A := B)).tendsto_mul_right b
  have hright : Tendsto (fun u : B => pure x u <• b)
      (CStarAlgebra.approximateUnit B) (𝓝 (pure x b)) := by
    have ht : Tendsto (fun u : B => pure x (u * b))
        (CStarAlgebra.approximateUnit B) (𝓝 (pure x b)) := by
      have hT := T.toContinuousLinearMap.continuous.continuousAt.tendsto.comp hu
      change Tendsto (fun u : B => T (u * b))
        (CStarAlgebra.approximateUnit B) (𝓝 (T b)) at hT
      simpa only [T, creationOnModel_apply] using hT
    refine ht.congr' (Eventually.of_forall fun u => ?_)
    simpa only [CStarModule.Right.right_smul_self] using
      hF.2.2.2.2.2.1 x u b
  exact tendsto_nhds_unique hleft hright

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

If g is surjective, the canonical vector map E → F has dense range.
-/
theorem canonicalBaseChangeMap_denseRange_of_surjective
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (hg : Function.Surjective g) : DenseRange (canonicalBaseChangeMap hF) := by
  let Q : Submodule ℂ F := LinearMap.range (canonicalBaseChangeMap hF).toLinearMap
  let P : Submodule ℂ F := Submodule.span ℂ
    (Set.range fun p : E × B => pure p.1 p.2)
  have hPQ : P ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, b⟩, rfl⟩
    obtain ⟨a, ha⟩ := hg b
    refine ⟨x <• a, ?_⟩
    change canonicalBaseChangeMap hF (x <• a) = pure x b
    rw [canonicalBaseChangeMap_right_smul, ha, canonicalBaseChangeMap_pure]
  have hP : P.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hF.2.2.2.2.2.2.2
  have hQ : Q.topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    rw [← hP]
    exact Submodule.topologicalClosure_mono hPQ
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hQ

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

For an adjointable endomorphism L of E and x ∈ E, its tensor extension satisfies L_F(j(x)) =
j(Lx).
-/
@[simp]
theorem mapLeftStarAlgHom_canonicalBaseChangeMap
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (L : AdjointableOperator.End A E) (x : E) :
    mapLeftStarAlgHom hF L (canonicalBaseChangeMap hF x) =
      canonicalBaseChangeMap hF (L x) := by
  obtain ⟨y, a, h⟩ :=
    CStarModule.exists_right_factor_of_starOrderedRing (B := A) (E := E) x
  rw [canonicalBaseChangeMap_factor hF x y a h, mapLeftStarAlgHom_pure]
  have hL : L x = L y <• a := by
    rw [h]
    exact L.map_right_smul y a
  exact (canonicalBaseChangeMap_factor hF (L x) (L y) a hL).symm

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

The tensor extension of the rank-one module operator determined by x, y ∈ E is the rank-one
operator determined by their canonical images j(x), j(y) ∈ F.
-/
@[simp]
theorem mapLeftStarAlgHom_rankOne_baseChange
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (x y : E) :
    mapLeftStarAlgHom hF (AdjointableOperator.rankOne (B := A) x y) =
      AdjointableOperator.rankOne (B := B)
        (canonicalBaseChangeMap hF x) (canonicalBaseChangeMap hF y) := by
  apply AdjointableOperator.toContinuousLinearMap_injective
  apply ContinuousLinearMap.ext_on hF.2.2.2.2.2.2.2
  rintro _ ⟨⟨z, b⟩, rfl⟩
  change mapLeftStarAlgHom hF (AdjointableOperator.rankOne (B := A) x y)
      (pure z b) =
    AdjointableOperator.rankOne (B := B)
      (canonicalBaseChangeMap hF x) (canonicalBaseChangeMap hF y) (pure z b)
  rw [← canonicalBaseChangeMap_pure hF z b]
  rw [(mapLeftStarAlgHom hF (AdjointableOperator.rankOne (B := A) x y)).map_right_smul,
    mapLeftStarAlgHom_canonicalBaseChangeMap,
    AdjointableOperator.rankOne_apply, canonicalBaseChangeMap_right_smul,
    ← canonicalBaseChangeMap_inner hF y z]
  rw [AdjointableOperator.map_right_smul, AdjointableOperator.rankOne_apply]

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

The tensor extension of a compact module endomorphism of E is a compact module endomorphism of
F.
-/
theorem mapLeftStarAlgHom_mem_compact_baseChange
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    {T : AdjointableOperator.End A E}
    (hT : T ∈ AdjointableOperator.compactSubmodule (B := A) (E := E) (F := E)) :
    mapLeftStarAlgHom hF T ∈
      AdjointableOperator.compactSubmodule (B := B) (E := F) (F := F) := by
  let Φ := mapLeftStarAlgHom hF
  let K := AdjointableOperator.compactSubmodule (B := B) (E := F) (F := F)
  let S : Submodule ℂ (AdjointableOperator.End A E) :=
    Submodule.comap (LinearMap.ofClass Φ) K
  have hSclosed : IsClosed (S : Set (AdjointableOperator.End A E)) :=
    AdjointableOperator.isClosed_compactSubmodule.preimage (map_continuous Φ)
  have hfinite : AdjointableOperator.finiteRankSubmodule
      (B := A) (E := E) (F := E) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change Φ (AdjointableOperator.rankOne (B := A) x y) ∈ K
    rw [mapLeftStarAlgHom_rankOne_baseChange hF]
    exact AdjointableOperator.rankOne_mem_compact _ _
  have hcompact : AdjointableOperator.compactSubmodule
      (B := A) (E := E) (F := E) ≤ S :=
    (AdjointableOperator.finiteRankSubmodule (B := A) (E := E) (F := E)).topologicalClosure_minimal
      hfinite hSclosed
  exact hcompact hT

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

Tensor extension along g restricts to a nonunital complex star homomorphism from the compact
module endomorphisms of E to those of F.
-/
def baseChangeCompactHom
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure) :
    AdjointableOperator.CompactEnd A E →⋆ₙₐ[ℂ] AdjointableOperator.CompactEnd B F :=
  NonUnitalStarAlgHom.codRestrict
    ((mapLeftStarAlgHom hF).toNonUnitalStarAlgHom.comp
      (NonUnitalStarSubalgebraClass.subtype
        (AdjointableOperator.compactStarSubalgebra (B := A) (E := E))))
    (AdjointableOperator.compactStarSubalgebra (B := B) (E := F))
    (fun T => mapLeftStarAlgHom_mem_compact_baseChange hF T.property)

/--
Let A and B be possibly nonunital complex C*-algebras, with star-compatible partial orders on
their opposite algebras. Let E and F be complete normed right inner-product modules over A and
B, respectively, with compatible complex normed-space structures. Let g : A → B be a nonunital
complex star homomorphism. Suppose pure : E × B → F satisfies the internal-tensor
complex-linearity, balancing, right-action and inner-product laws for the left multiplication
representation induced by g, and has dense complex-linear span in F.

For a compact endomorphism T of E, the induced compact endomorphism of F has underlying
adjointable map equal to the tensor extension of T.
-/
@[simp]
theorem baseChangeCompactHom_apply
    (hF : IsModel ((AdjointableOperator.leftRegular (B := B)).comp g) pure)
    (T : AdjointableOperator.CompactEnd A E) :
    (baseChangeCompactHom hF T : AdjointableOperator.End B F) =
      mapLeftStarAlgHom hF (T : AdjointableOperator.End A E) := by
  rfl

end CStarModule.InternalTensorProduct.IsModel
