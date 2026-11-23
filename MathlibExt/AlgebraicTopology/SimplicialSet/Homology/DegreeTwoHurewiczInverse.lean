/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.DegreeTwoHurewiczGenerators
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyGroupCommutativity
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyGroupTetrahedralRelation
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Degree-two Hurewicz for one-reduced Kan complexes

The inverse is constructed on the original normalized integral two-chains by
sending simplex generators to their native second homotopy classes. The exact
signed three-boundaries vanish by the native tetrahedral relation. Descent
through the actual homology cokernel and the original generator formulas
prove both inverse identities.

The implementation records the two elementary homotopy laws explicitly.
The public one-reduced endpoints below instantiate those laws from the actual
commutativity and tetrahedral theorems. Their only mathematical hypotheses are
the Kan condition, a chosen vertex, and literal edge degeneracy.

Proof-only implementation lemmas are private where the public data permits.
The data helpers and the literal-face tetrahedral bridge remain visible where
the public bundled group and normalized-chain maps depend on their types or
values; their native multiplication, unit, and coefficient object are fixed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped Simplicial

universe u

namespace SSet.DegreeTwoHurewiczInverse

/-- Integer coefficients, `AlgebraicTopology.singularIntegralCoefficients` (`ULift ℤ`). -/
abbrev Z : AddCommGrpCat.{u} :=
  AlgebraicTopology.singularIntegralCoefficients

/-- The normalized chain complex of `X` with integer coefficients `Z`. -/
abbrev N (X : SSet.{u}) := X.normalizedChainComplex (Z : AddCommGrpCat.{u})

variable {X : SSet.{u}} [KanComplex X]

/-- The exact signature of the already-proved pointed tetrahedral relation.
The implementation uses this literal-face interface; the canonical endpoints
instantiate the actual theorem below. -/
abbrev TetrahedralLaw (x : X _⦋0⦌) : Prop :=
  ∀ (t : Δ[3] ⟶ X) (p₀ p₁ p₂ p₃ : X.PtSimplex 2 x),
    stdSimplex.δ (0 : Fin 4) ≫ t = RelativeMorphism.map p₀ →
    stdSimplex.δ (1 : Fin 4) ≫ t = RelativeMorphism.map p₁ →
    stdSimplex.δ (2 : Fin 4) ≫ t = RelativeMorphism.map p₂ →
    stdSimplex.δ (3 : Fin 4) ≫ t = RelativeMorphism.map p₃ →
    KanComplex.π.mk p₀ * KanComplex.π.mk p₂ =
      KanComplex.π.mk p₃ * KanComplex.π.mk p₁

/-- The native group structure on `π₂(X, x)` as a commutative group, given the
commutativity law `hcomm`. -/
@[instance_reducible]
def piTwoCommGroup (x : X _⦋0⦌)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a) :
    CommGroup (KanComplex.π 2 X x) :=
  { (KanComplex.π.group (n := 1) (X := X) (x := x)) with
    mul_comm := hcomm }

/-- The additive interpretation of the actual native second homotopy group.
Its multiplication and unit come from the existing native group structure. -/
noncomputable def piTwoAddCommGrp (x : X _⦋0⦌)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a) :
    AddCommGrpCat.{u} := by
  letI := piTwoCommGroup x hcomm
  exact AddCommGrpCat.of (Additive (KanComplex.π 2 X x))

/-- The standard additive type tag, with its codomain kept as the fixed
bundled native group so instance search cannot change the native unit. -/
def piTwoOfMul (x : X _⦋0⦌)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (a : KanComplex.π 2 X x) : piTwoAddCommGrp x hcomm :=
  Additive.ofMul a

/-- Recover the original native class from its additive type tag. -/
def piTwoToMul (x : X _⦋0⦌)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (a : piTwoAddCommGrp x hcomm) : KanComplex.π 2 X x :=
  Additive.toMul a

@[simp]
private theorem piTwoToMul_ofMul (x : X _⦋0⦌)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (a : KanComplex.π 2 X x) :
    piTwoToMul x hcomm (piTwoOfMul x hcomm a) = a :=
  rfl

@[simp]
private theorem piTwoOfMul_toMul (x : X _⦋0⦌)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (a : piTwoAddCommGrp x hcomm) :
    piTwoOfMul x hcomm (piTwoToMul x hcomm a) = a :=
  rfl

/-- The native class of an original two-simplex with the canonical pointed
boundary supplied by edge degeneracy. -/
noncomputable def simplexPiClass (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (s : X _⦋2⦌) : piTwoAddCommGrp x hcomm :=
  piTwoOfMul x hcomm (KanComplex.π.mk
    (MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge s))

omit [KanComplex X] in
private theorem pointedOfDegenerate_eq_const (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (s : X _⦋2⦌) (hs : s ∈ X.degenerate 2) :
    MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge s =
      (RelativeMorphism.const : X.PtSimplex 2 x) := by
  simp only [degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hs
  obtain ⟨i, e, rfl⟩ := hs
  apply RelativeMorphism.ext
  change yonedaEquiv.symm (X.σ i e) = const x
  rw [hedge e, σ_zero_eq_yonedaEquiv_const,
    ← stdSimplex.yonedaEquiv_σ_comp, comp_const,
    Equiv.symm_apply_apply]

/-- Degenerate original two-simplices have zero native additive class. -/
private theorem simplexPiClass_eq_zero_of_degenerate (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (s : X _⦋2⦌) (hs : s ∈ X.degenerate 2) :
    simplexPiClass x hedge hcomm s = 0 := by
  change Additive.ofMul (KanComplex.π.mk
      (MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge s)) =
    Additive.ofMul ((KanComplex.π.group (n := 1) (X := X) (x := x)).one)
  rw [KanComplex.π.group_one_eq_instOne, pointedOfDegenerate_eq_const x hedge s hs]
  rfl

/-- The integral coefficient map sending the positive generator to the native
class of the original two-simplex. This is the standard corepresentable
coefficient map, not an inverse to Hurewicz. -/
noncomputable def simplexPiCoefficient (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (s : X _⦋2⦌) : Z ⟶ piTwoAddCommGrp x hcomm :=
  (AddCommGrpCat.uliftZMultiplesAddEquiv (piTwoAddCommGrp x hcomm)).symm
    (simplexPiClass x hedge hcomm s)

private theorem simplexPiCoefficient_one (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (s : X _⦋2⦌) :
    simplexPiCoefficient x hedge hcomm s (ULift.up (1 : ℤ)) =
      simplexPiClass x hedge hcomm s := by
  change (uliftZMultiplesHom (piTwoAddCommGrp x hcomm)
      (simplexPiClass x hedge hcomm s)) (ULift.up (1 : ℤ)) = _
  rw [uliftZMultiplesHom_apply_apply]
  have hup : AddEquiv.ulift (ULift.up (1 : ℤ) : ULift.{u} ℤ) = 1 := rfl
  rw [hup, one_zsmul]

private theorem simplexPiCoefficient_eq_zero_of_degenerate (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (s : X _⦋2⦌) (hs : s ∈ X.degenerate 2) :
    simplexPiCoefficient x hedge hcomm s = 0 := by
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv (piTwoAddCommGrp x hcomm)).injective
  rw [simplexPiCoefficient, AddEquiv.apply_symm_apply, map_zero,
    simplexPiClass_eq_zero_of_degenerate x hedge hcomm s hs]

/-- Extend original nondegenerate simplex classes along the actual normalized
chain coproduct presentation. This is an additive, hence integral-linear, map. -/
noncomputable def normalizedTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a) :
    (N X).X 2 ⟶ piTwoAddCommGrp x hcomm :=
  (X.isColimitCofanNormalizedChainComplex (Z : AddCommGrpCat.{u}) 2).desc
    (Cofan.mk (piTwoAddCommGrp x hcomm)
      (fun s : X.nonDegenerate 2 => simplexPiCoefficient x hedge hcomm s.val))

@[reassoc]
private theorem ι_comp_normalizedTwoToPi_of_nonDegenerate (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (s : X _⦋2⦌) (hs : s ∈ X.nonDegenerate 2) :
    X.ιNormalizedChainComplex (R := (Z : AddCommGrpCat.{u})) s ≫
        normalizedTwoToPi x hedge hcomm = simplexPiCoefficient x hedge hcomm s := by
  exact (X.isColimitCofanNormalizedChainComplex (Z : AddCommGrpCat.{u}) 2).fac
    (Cofan.mk (piTwoAddCommGrp x hcomm)
      (fun t : X.nonDegenerate 2 => simplexPiCoefficient x hedge hcomm t.val))
    ⟨⟨s, hs⟩⟩

@[reassoc]
private theorem ι_comp_normalizedTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (s : X _⦋2⦌) :
    X.ιNormalizedChainComplex (R := (Z : AddCommGrpCat.{u})) s ≫
        normalizedTwoToPi x hedge hcomm = simplexPiCoefficient x hedge hcomm s := by
  by_cases hs : s ∈ X.degenerate 2
  · rw [X.ιNormalizedChainComplex_eq_zero s hs, zero_comp,
      simplexPiCoefficient_eq_zero_of_degenerate x hedge hcomm s hs]
  · exact ι_comp_normalizedTwoToPi_of_nonDegenerate x hedge hcomm s hs

/-- The exact signed face relation follows from the provided native
tetrahedral law and the already-proved native commutativity law. -/
private theorem signedSimplexPiClass (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) (s : X _⦋3⦌) :
    (∑ i : Fin 4, (-1 : ℤ) ^ i.val •
      simplexPiClass x hedge hcomm (X.δ i s)) = 0 := by
  let _ := piTwoCommGroup x hcomm
  let p (i : Fin 4) := MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge (X.δ i s)
  have hp (i : Fin 4) : stdSimplex.δ i ≫ yonedaEquiv.symm s = RelativeMorphism.map (p i) := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    rfl
  have hm := htetra (yonedaEquiv.symm s) (p 0) (p 1) (p 2) (p 3)
    (hp 0) (hp 1) (hp 2) (hp 3)
  have ha : simplexPiClass x hedge hcomm (X.δ 0 s) +
        simplexPiClass x hedge hcomm (X.δ 2 s) =
      simplexPiClass x hedge hcomm (X.δ 3 s) +
        simplexPiClass x hedge hcomm (X.δ 1 s) := by
    change Additive.ofMul (KanComplex.π.mk (p 0) * KanComplex.π.mk (p 2)) =
      Additive.ofMul (KanComplex.π.mk (p 3) * KanComplex.π.mk (p 1))
    exact congrArg Additive.ofMul hm
  have hs : simplexPiClass x hedge hcomm (X.δ 0 s) -
        simplexPiClass x hedge hcomm (X.δ 1 s) +
        simplexPiClass x hedge hcomm (X.δ 2 s) -
        simplexPiClass x hedge hcomm (X.δ 3 s) = 0 := by
    calc
      _ = (simplexPiClass x hedge hcomm (X.δ 0 s) +
            simplexPiClass x hedge hcomm (X.δ 2 s)) -
          (simplexPiClass x hedge hcomm (X.δ 3 s) +
            simplexPiClass x hedge hcomm (X.δ 1 s)) := by abel
      _ = 0 := sub_eq_zero.mpr ha
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hs

/-- The actual normalized integral three-boundary is killed by the native
two-chain class map. Boundary vanishing is derived here, not assumed. -/
private theorem d_comp_normalizedTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) :
    (N X).d 3 2 ≫ normalizedTwoToPi x hedge hcomm = 0 := by
  apply X.normalizedChainComplex_hom_ext
  intro s _
  rw [← Category.assoc, ιNormalizedChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ι_comp_normalizedTwoToPi, comp_zero]
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv (piTwoAddCommGrp x hcomm)).injective
  simp only [map_sum, map_zsmul, map_zero, simplexPiCoefficient,
    AddEquiv.apply_symm_apply]
  exact signedSimplexPiClass x hedge hcomm htetra s

/-- Descend the actual normalized chain class through the actual homology
cokernel. The condition needed for descent is proved by the signed boundary
calculation above. -/
noncomputable def homologyTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) :
    (N X).homology 2 ⟶ piTwoAddCommGrp x hcomm :=
  ((N X).homologyIsCokernel (i := 3) (j := 2) (by simp)).desc
    (CokernelCofork.ofπ
      ((N X).iCycles 2 ≫ normalizedTwoToPi x hedge hcomm)
      (by
        rw [← Category.assoc, HomologicalComplex.toCycles_i]
        exact d_comp_normalizedTwoToPi x hedge hcomm htetra))

@[reassoc]
private theorem homologyπ_comp_homologyTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) :
    (N X).homologyπ 2 ≫ homologyTwoToPi x hedge hcomm htetra =
      (N X).iCycles 2 ≫ normalizedTwoToPi x hedge hcomm := by
  dsimp only [homologyTwoToPi]
  exact Cofork.IsColimit.π_desc
    ((N X).homologyIsCokernel (i := 3) (j := 2) (by simp))

@[reassoc]
private theorem normalizedTwoToHomology_comp_homologyTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) :
    normalizedTwoToHomology x hedge ≫ homologyTwoToPi x hedge hcomm htetra =
      normalizedTwoToPi x hedge hcomm := by
  rw [normalizedTwoToHomology, Category.assoc, homologyπ_comp_homologyTwoToPi,
    ← Category.assoc, HomologicalComplex.liftCycles_i, Category.id_comp]

omit [KanComplex X] in
private theorem pointedOfPointed_eq (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (p : X.PtSimplex 2 x) :
    MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge
        (yonedaEquiv (RelativeMorphism.map p)) = p := by
  apply RelativeMorphism.ext
  rw [MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate_map, Equiv.symm_apply_apply]

@[reassoc]
private theorem pointedTwoHomologyClass_comp_homologyTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) (p : X.PtSimplex 2 x) :
    pointedTwoHomologyClass p ≫ homologyTwoToPi x hedge hcomm htetra =
      simplexPiCoefficient x hedge hcomm (yonedaEquiv (RelativeMorphism.map p)) := by
  have he :
      X.ιNormalizedChainComplex (R := (Z : AddCommGrpCat.{u}))
          (yonedaEquiv (RelativeMorphism.map p)) ≫
          normalizedTwoToHomology x hedge = pointedTwoHomologyClass p := by
    simpa only [pointedOfPointed_eq x hedge p] using
      ιNormalizedChainComplex_comp_normalizedTwoToHomology x hedge
        (yonedaEquiv (RelativeMorphism.map p))
  rw [← he, Category.assoc, normalizedTwoToHomology_comp_homologyTwoToPi,
    ι_comp_normalizedTwoToPi]

/-- Exact original pointed-simplex formula for the descended map. -/
private theorem homologyTwoToPi_pointed (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) (p : X.PtSimplex 2 x) :
    homologyTwoToPi x hedge hcomm htetra
        (pointedTwoHomologyClass p (ULift.up (1 : ℤ))) =
      piTwoOfMul x hcomm (KanComplex.π.mk p) := by
  have h := ConcreteCategory.congr_hom
    (pointedTwoHomologyClass_comp_homologyTwoToPi x hedge hcomm htetra p)
    (ULift.up (1 : ℤ))
  change homologyTwoToPi x hedge hcomm htetra
      (pointedTwoHomologyClass p (ULift.up (1 : ℤ))) =
    simplexPiCoefficient x hedge hcomm
      (yonedaEquiv (RelativeMorphism.map p)) (ULift.up (1 : ℤ)) at h
  rw [simplexPiCoefficient_one, simplexPiClass, pointedOfPointed_eq x hedge p] at h
  exact h

/-- The same representative formula in the original native carrier. -/
private theorem homologyTwoToPi_pointed_toMul (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) (p : X.PtSimplex 2 x) :
    piTwoToMul x hcomm (homologyTwoToPi x hedge hcomm htetra
      (pointedTwoHomologyClass p (ULift.up (1 : ℤ)))) = KanComplex.π.mk p := by
  rw [homologyTwoToPi_pointed, piTwoToMul_ofMul]

/-- The additive categorical form of the existing element-valued Hurewicz
homomorphism, without changing its function or its native multiplication. -/
noncomputable def nativeHurewicz (x : X _⦋0⦌)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a) :
    piTwoAddCommGrp x hcomm ⟶ (N X).homology 2 := by
  letI := piTwoCommGroup x hcomm
  exact AddCommGrpCat.ofHom (degreeTwoHurewiczElementMulHom x).toAdditiveLeft

@[simp]
private theorem nativeHurewicz_mk (x : X _⦋0⦌)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (p : X.PtSimplex 2 x) :
    nativeHurewicz x hcomm (piTwoOfMul x hcomm (KanComplex.π.mk p)) =
      pointedTwoHomologyClass p (ULift.up (1 : ℤ)) :=
  rfl

@[reassoc]
private theorem simplexPiCoefficient_comp_nativeHurewicz (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (s : X _⦋2⦌) :
    simplexPiCoefficient x hedge hcomm s ≫ nativeHurewicz x hcomm =
      pointedTwoHomologyClass
        (MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge s) := by
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv ((N X).homology 2)).injective
  change nativeHurewicz x hcomm
      (simplexPiCoefficient x hedge hcomm s (ULift.up (1 : ℤ))) =
    pointedTwoHomologyClass
      (MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge s)
      (ULift.up (1 : ℤ))
  rw [simplexPiCoefficient_one]
  rfl

@[reassoc]
private theorem normalizedTwoToPi_comp_nativeHurewicz (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a) :
    normalizedTwoToPi x hedge hcomm ≫ nativeHurewicz x hcomm =
      normalizedTwoToHomology x hedge := by
  apply X.normalizedChainComplex_hom_ext
  intro s _
  rw [← Category.assoc, ι_comp_normalizedTwoToPi,
    simplexPiCoefficient_comp_nativeHurewicz,
    ιNormalizedChainComplex_comp_normalizedTwoToHomology]

/-- The descended map is a left inverse on every native homotopy class,
using the original pointed representative formula. -/
@[reassoc]
private theorem nativeHurewicz_comp_homologyTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) :
    nativeHurewicz x hcomm ≫ homologyTwoToPi x hedge hcomm htetra =
      𝟙 (piTwoAddCommGrp x hcomm) := by
  ext a
  change homologyTwoToPi x hedge hcomm htetra (nativeHurewicz x hcomm a) = a
  obtain ⟨p, hp⟩ := KanComplex.π.mk_surjective (piTwoToMul x hcomm a)
  have ha : a = piTwoOfMul x hcomm (KanComplex.π.mk p) := by
    calc
      a = piTwoOfMul x hcomm (piTwoToMul x hcomm a) :=
        (piTwoOfMul_toMul x hcomm a).symm
      _ = piTwoOfMul x hcomm (KanComplex.π.mk p) :=
        congrArg (piTwoOfMul x hcomm) hp.symm
  rw [ha, nativeHurewicz_mk, homologyTwoToPi_pointed]

/-- The right inverse identity is checked through the actual epic map from
normalized chains to homology and its original generator characteristics. -/
@[reassoc]
private theorem homologyTwoToPi_comp_nativeHurewicz (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) :
    homologyTwoToPi x hedge hcomm htetra ≫ nativeHurewicz x hcomm =
      𝟙 ((N X).homology 2) := by
  apply (cancel_epi (normalizedTwoToHomology x hedge)).mp
  rw [← Category.assoc, normalizedTwoToHomology_comp_homologyTwoToPi,
    normalizedTwoToPi_comp_nativeHurewicz, Category.comp_id]

/-- Injectivity is deduced from the constructed normalized homology descent;
it is not a prerequisite supplied to that construction. -/
private theorem degreeTwoHurewiczElementMulHom_injective_of_laws (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (hcomm : ∀ a b : KanComplex.π 2 X x, a * b = b * a)
    (htetra : TetrahedralLaw (X := X) x) :
    Function.Injective (degreeTwoHurewiczElementMulHom x) := by
  intro a b hab
  have he := congrArg
    (fun z => homologyTwoToPi x hedge hcomm htetra (Multiplicative.toAdd z)) hab
  change homologyTwoToPi x hedge hcomm htetra
      (nativeHurewicz x hcomm (piTwoOfMul x hcomm a)) =
    homologyTwoToPi x hedge hcomm htetra
      (nativeHurewicz x hcomm (piTwoOfMul x hcomm b)) at he
  have ha := ConcreteCategory.congr_hom
    (nativeHurewicz_comp_homologyTwoToPi x hedge hcomm htetra) (piTwoOfMul x hcomm a)
  have hb := ConcreteCategory.congr_hom
    (nativeHurewicz_comp_homologyTwoToPi x hedge hcomm htetra) (piTwoOfMul x hcomm b)
  change homologyTwoToPi x hedge hcomm htetra
      (nativeHurewicz x hcomm (piTwoOfMul x hcomm a)) = piTwoOfMul x hcomm a at ha
  change homologyTwoToPi x hedge hcomm htetra
      (nativeHurewicz x hcomm (piTwoOfMul x hcomm b)) = piTwoOfMul x hcomm b at hb
  rw [ha, hb] at he
  exact congrArg (piTwoToMul x hcomm) he

/-- Convert the actual edge-degenerate tetrahedral theorem to the literal-face
interface used by the reusable inverse construction. The pointed maps are
unchanged; this proof only identifies the canonical face representatives. -/
theorem tetrahedralLawOfEdges (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) : TetrahedralLaw (X := X) x := by
  intro t p₀ p₁ p₂ p₃ h₀ h₁ h₂ h₃
  let q (i : Fin 4) := MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge
    (X.δ i (yonedaEquiv t))
  have hq (i : Fin 4) (p : X.PtSimplex 2 x)
      (hp : stdSimplex.δ i ≫ t = RelativeMorphism.map p) : q i = p := by
    apply RelativeMorphism.ext
    change yonedaEquiv.symm (X.δ i (yonedaEquiv t)) = RelativeMorphism.map p
    rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply, hp]
  have h := KanComplex.π.tetrahedral_relation_of_edges_degenerate x hedge (yonedaEquiv t)
  change KanComplex.π.mk (q 0) * KanComplex.π.mk (q 2) =
    KanComplex.π.mk (q 3) * KanComplex.π.mk (q 1) at h
  rw [hq 0 p₀ h₀, hq 1 p₁ h₁, hq 2 p₂ h₂, hq 3 p₃ h₃] at h
  exact h

end SSet.DegreeTwoHurewiczInverse

namespace SSet

variable {X : SSet.{u}} [KanComplex X]

/-- The additive group of actual native second homotopy classes. The existing
native multiplication and unit are retained, with commutativity now proved. -/
noncomputable abbrev nativePiTwoAddCommGrp (x : X _⦋0⦌) : AddCommGrpCat.{u} :=
  DegreeTwoHurewiczInverse.piTwoAddCommGrp x (KanComplex.π.mul_comm_two x)

/-- Regard an original native class as an element of its additive group. -/
def nativePiTwoOfMul (x : X _⦋0⦌) (a : KanComplex.π 2 X x) : nativePiTwoAddCommGrp x :=
  DegreeTwoHurewiczInverse.piTwoOfMul x (KanComplex.π.mul_comm_two x) a

/-- Recover the original native class from its additive interpretation. -/
def nativePiTwoToMul (x : X _⦋0⦌) (a : nativePiTwoAddCommGrp x) : KanComplex.π 2 X x :=
  DegreeTwoHurewiczInverse.piTwoToMul x (KanComplex.π.mul_comm_two x) a

/-- The original native unit is zero in its fixed additive interpretation. -/
@[simp]
theorem nativePiTwoOfMul_one (x : X _⦋0⦌) :
    nativePiTwoOfMul x (1 : KanComplex.π 2 X x) = 0 := by
  change Additive.ofMul (1 : KanComplex.π 2 X x) =
    Additive.ofMul ((KanComplex.π.group (n := 1) (X := X) (x := x)).one)
  exact congrArg (Additive.ofMul : KanComplex.π 2 X x → Additive (KanComplex.π 2 X x))
    (KanComplex.π.group_one_eq_instOne (n := 1) (X := X) (x := x)).symm

/-- Additive zero recovers the original native unit. -/
@[simp]
theorem nativePiTwoToMul_zero (x : X _⦋0⦌) :
    nativePiTwoToMul x (0 : nativePiTwoAddCommGrp x) = 1 := by
  change (KanComplex.π.group (n := 1) (X := X) (x := x)).one =
    (1 : KanComplex.π 2 X x)
  exact KanComplex.π.group_one_eq_instOne

/-- The original two-simplex class with its canonical pointed boundary. -/
noncomputable def simplexPiClass (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋2⦌) : nativePiTwoAddCommGrp x :=
  DegreeTwoHurewiczInverse.simplexPiClass x hedge (KanComplex.π.mul_comm_two x) s

/-- The integral coefficient map with the original native class as its positive generator. -/
noncomputable def simplexPiCoefficient (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋2⦌) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      nativePiTwoAddCommGrp x :=
  DegreeTwoHurewiczInverse.simplexPiCoefficient x hedge (KanComplex.π.mul_comm_two x) s

/-- The actual normalized integral two-chain class map. -/
noncomputable def normalizedTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) :
    (X.normalizedChainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).X 2 ⟶
        nativePiTwoAddCommGrp x :=
  DegreeTwoHurewiczInverse.normalizedTwoToPi x hedge (KanComplex.π.mul_comm_two x)

@[reassoc]
theorem ι_comp_normalizedTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋2⦌) :
    X.ιNormalizedChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) s ≫
      normalizedTwoToPi x hedge = simplexPiCoefficient x hedge s :=
  DegreeTwoHurewiczInverse.ι_comp_normalizedTwoToPi x hedge (KanComplex.π.mul_comm_two x) s

theorem simplexPiCoefficient_one (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋2⦌) :
    simplexPiCoefficient x hedge s (ULift.up (1 : ℤ)) = simplexPiClass x hedge s :=
  DegreeTwoHurewiczInverse.simplexPiCoefficient_one x hedge (KanComplex.π.mul_comm_two x) s

theorem simplexPiClass_eq_zero_of_degenerate (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋2⦌) (hs : s ∈ X.degenerate 2) :
    simplexPiClass x hedge s = 0 :=
  DegreeTwoHurewiczInverse.simplexPiClass_eq_zero_of_degenerate x hedge
    (KanComplex.π.mul_comm_two x) s hs

theorem simplexPiCoefficient_eq_zero_of_degenerate (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋2⦌) (hs : s ∈ X.degenerate 2) :
    simplexPiCoefficient x hedge s = 0 :=
  DegreeTwoHurewiczInverse.simplexPiCoefficient_eq_zero_of_degenerate x hedge
    (KanComplex.π.mul_comm_two x) s hs

/-- Every actual tetrahedron has the exact normalized integral sign relation. -/
theorem signedSimplexPiClass (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (s : X _⦋3⦌) :
    (∑ i : Fin 4, (-1 : ℤ) ^ i.val • simplexPiClass x hedge (X.δ i s)) = 0 :=
  DegreeTwoHurewiczInverse.signedSimplexPiClass x hedge (KanComplex.π.mul_comm_two x)
    (DegreeTwoHurewiczInverse.tetrahedralLawOfEdges x hedge) s

/-- Every actual normalized three-boundary maps to zero. -/
theorem d_comp_normalizedTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) :
    (X.normalizedChainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 3 2 ≫
        normalizedTwoToPi x hedge = 0 :=
  DegreeTwoHurewiczInverse.d_comp_normalizedTwoToPi x hedge (KanComplex.π.mul_comm_two x)
    (DegreeTwoHurewiczInverse.tetrahedralLawOfEdges x hedge)

/-- The descended map from the original normalized homology object. -/
noncomputable def homologyTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) :
    (X.normalizedChainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2 ⟶
        nativePiTwoAddCommGrp x :=
  DegreeTwoHurewiczInverse.homologyTwoToPi x hedge (KanComplex.π.mul_comm_two x)
    (DegreeTwoHurewiczInverse.tetrahedralLawOfEdges x hedge)

@[reassoc]
theorem homologyπ_comp_homologyTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) :
    (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 2 ≫
      homologyTwoToPi x hedge =
    (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles 2 ≫
      normalizedTwoToPi x hedge :=
  DegreeTwoHurewiczInverse.homologyπ_comp_homologyTwoToPi x hedge
    (KanComplex.π.mul_comm_two x) (DegreeTwoHurewiczInverse.tetrahedralLawOfEdges x hedge)

theorem homologyTwoToPi_pointed (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (p : X.PtSimplex 2 x) :
    homologyTwoToPi x hedge (pointedTwoHomologyClass p (ULift.up (1 : ℤ))) =
      nativePiTwoOfMul x (KanComplex.π.mk p) :=
  DegreeTwoHurewiczInverse.homologyTwoToPi_pointed x hedge (KanComplex.π.mul_comm_two x)
    (DegreeTwoHurewiczInverse.tetrahedralLawOfEdges x hedge) p

/-- The class map has the exact original pointed-generator characteristic. -/
theorem normalizedTwoToPi_pointed (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (p : X.PtSimplex 2 x) :
    normalizedTwoToPi x hedge (pointedTwoGenerator p (ULift.up (1 : ℤ))) =
      nativePiTwoOfMul x (KanComplex.π.mk p) := by
  have h := ConcreteCategory.congr_hom
    (ι_comp_normalizedTwoToPi x hedge (yonedaEquiv (RelativeMorphism.map p)))
    (ULift.up (1 : ℤ))
  change normalizedTwoToPi x hedge (pointedTwoGenerator p (ULift.up (1 : ℤ))) =
    simplexPiCoefficient x hedge (yonedaEquiv (RelativeMorphism.map p))
      (ULift.up (1 : ℤ)) at h
  rw [simplexPiCoefficient_one] at h
  change normalizedTwoToPi x hedge (pointedTwoGenerator p (ULift.up (1 : ℤ))) =
    DegreeTwoHurewiczInverse.simplexPiClass x hedge (KanComplex.π.mul_comm_two x)
      (yonedaEquiv (RelativeMorphism.map p)) at h
  rw [DegreeTwoHurewiczInverse.simplexPiClass,
    DegreeTwoHurewiczInverse.pointedOfPointed_eq x hedge p] at h
  exact h

/-- The original native Hurewicz homomorphism in additive categorical form. -/
noncomputable def nativeHurewicz (x : X _⦋0⦌) :
    nativePiTwoAddCommGrp x ⟶
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2 :=
  DegreeTwoHurewiczInverse.nativeHurewicz x (KanComplex.π.mul_comm_two x)

@[reassoc]
theorem nativeHurewicz_comp_homologyTwoToPi (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) :
    nativeHurewicz x ≫ homologyTwoToPi x hedge = 𝟙 (nativePiTwoAddCommGrp x) :=
  DegreeTwoHurewiczInverse.nativeHurewicz_comp_homologyTwoToPi x hedge
    (KanComplex.π.mul_comm_two x) (DegreeTwoHurewiczInverse.tetrahedralLawOfEdges x hedge)

@[reassoc]
theorem homologyTwoToPi_comp_nativeHurewicz (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) :
    homologyTwoToPi x hedge ≫ nativeHurewicz x =
      𝟙 ((X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2) :=
  DegreeTwoHurewiczInverse.homologyTwoToPi_comp_nativeHurewicz x hedge
    (KanComplex.π.mul_comm_two x) (DegreeTwoHurewiczInverse.tetrahedralLawOfEdges x hedge)

/-- Bijectivity of the actual native Hurewicz homomorphism in a one-reduced Kan complex. -/
theorem degreeTwoHurewiczElementMulHom_bijective (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) :
    Function.Bijective (degreeTwoHurewiczElementMulHom x) :=
  ⟨DegreeTwoHurewiczInverse.degreeTwoHurewiczElementMulHom_injective_of_laws x hedge
      (KanComplex.π.mul_comm_two x) (DegreeTwoHurewiczInverse.tetrahedralLawOfEdges x hedge),
    degreeTwoHurewiczElementMulHom_surjective x hedge⟩

/-- The canonical one-reduced degree-two Hurewicz equivalence, preserving
the existing native multiplication and exact forward map. -/
noncomputable def degreeTwoHurewiczEquiv (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) :
    KanComplex.π 2 X x ≃* Multiplicative
      ((X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2) :=
  MulEquiv.ofBijective (degreeTwoHurewiczElementMulHom x)
    (degreeTwoHurewiczElementMulHom_bijective x hedge)

@[simp]
theorem degreeTwoHurewiczEquiv_apply (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (a : KanComplex.π 2 X x) :
    degreeTwoHurewiczEquiv x hedge a = degreeTwoHurewiczElementMulHom x a :=
  rfl

@[simp]
theorem degreeTwoHurewiczEquiv_mk (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (p : X.PtSimplex 2 x) :
    degreeTwoHurewiczEquiv x hedge (KanComplex.π.mk p) =
      Multiplicative.ofAdd (pointedTwoHomologyClass p (ULift.up (1 : ℤ))) :=
  degreeTwoHurewiczElementMulHom_mk x p

@[simp]
theorem degreeTwoHurewiczEquiv_symm_pointed (x : X _⦋0⦌)
    (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x) (p : X.PtSimplex 2 x) :
    (degreeTwoHurewiczEquiv x hedge).symm
        (Multiplicative.ofAdd (pointedTwoHomologyClass p (ULift.up (1 : ℤ)))) =
      KanComplex.π.mk p := by
  rw [← degreeTwoHurewiczEquiv_mk x hedge p, MulEquiv.symm_apply_apply]

end SSet
