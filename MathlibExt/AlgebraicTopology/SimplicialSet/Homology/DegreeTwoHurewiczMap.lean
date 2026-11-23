/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroupUnit
public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedHomologyComparison
public import MathlibExt.AlgebraicTopology.SingularHomology.Integral

/-!
# The native degree two Hurewicz map

A pointed two-simplex has three constant one-dimensional faces.  Its
normalized integral generator is therefore a cycle and determines a class in
normalized `H₂`.  The signed boundary of a `RelStruct₀` three-simplex shows
that this class depends only on the native `π₂` class.  The signed boundary
of a `MulStruct` filler proves compatibility with the native product.

The resulting Hurewicz homomorphism is defined for every Kan complex.  No
connectedness, minimality, edge-degeneracy, injectivity, surjectivity, or
equivalence is asserted in this file.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped Simplicial

universe u

namespace SSet


/-- The normalized integral generator of a positive-dimensional constant
simplex is zero. -/
theorem ιNormalizedChainComplex_yonedaEquiv_const_eq_zero
    {X : SSet.{u}} (n : ℕ) (x : X _⦋0⦌) :
    X.ιNormalizedChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
        (SSet.yonedaEquiv (SSet.const x : Δ[n + 1] ⟶ X)) = 0 := by
  have hconst :
      SSet.yonedaEquiv (SSet.const x : Δ[n + 1] ⟶ X) =
        X.σ 0 (SSet.yonedaEquiv (SSet.const x : Δ[n] ⟶ X)) := by
    rw [← SSet.stdSimplex.yonedaEquiv_σ_comp]
    rw [SSet.comp_const]
  rw [hconst]
  apply X.ιNormalizedChainComplex_eq_zero
  simp only [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion,
    Set.mem_range]
  exact ⟨0, _, rfl⟩

/-- The normalized integral two-chain generator underlying a pointed
two-simplex. -/
noncomputable def pointedTwoGenerator
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).X 2 :=
  X.ιNormalizedChainComplex
    (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
    (SSet.yonedaEquiv (RelativeMorphism.map p))

/-- Every face of a pointed two-simplex has zero normalized integral
generator. -/
theorem pointedTwoGenerator_face_eq_zero
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x)
    (i : Fin 3) :
    X.ιNormalizedChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
        (X.δ i (SSet.yonedaEquiv (RelativeMorphism.map p))) = 0 := by
  rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.PtSimplex.δ_map,
    ιNormalizedChainComplex_yonedaEquiv_const_eq_zero (n := 0)]

/-- The normalized generator of a pointed two-simplex is a cycle. -/
theorem pointedTwoGenerator_cycle
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x) :
    pointedTwoGenerator p ≫
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 2 1 = 0 := by
  rw [pointedTwoGenerator, SSet.ιNormalizedChainComplex_d]
  simp_rw [pointedTwoGenerator_face_eq_zero p]
  simp

/-- The normalized integral two-cycle represented by a pointed two-simplex. -/
noncomputable def pointedTwoCycle
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).cycles 2 :=
  let K := X.normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  K.liftCycles (pointedTwoGenerator p) 1 (by simp)
    (pointedTwoGenerator_cycle p)

/-- The pointed two-cycle includes as the original normalized simplex
generator. -/
@[reassoc (attr := simp)]
theorem pointedTwoCycle_i
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x) :
    pointedTwoCycle p ≫
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles 2 =
      pointedTwoGenerator p := by
  dsimp [pointedTwoCycle]
  apply HomologicalComplex.liftCycles_i

/-- The normalized integral `H₂` class of a pointed two-simplex. -/
noncomputable def pointedTwoHomologyClass
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x) :
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homology 2 :=
  pointedTwoCycle p ≫
    (X.normalizedChainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 2

/-- A normalized degree-three boundary has zero class in normalized `H₂`. -/
theorem normalizedThreeBoundary_homology_eq_zero
    {X : SSet.{u}}
    (c : (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).X 3) :
    c ≫ (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).toCycles 3 2 ≫
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 2 = 0 := by
  simp

/-- Two pointed two-cycles have the same homology class when the difference
of their normalized generators is a degree-three boundary. -/
theorem pointedTwoHomologyClass_eq_of_sub_eq_boundary
    {X : SSet.{u}} {x : X _⦋0⦌} {p q : X.PtSimplex 2 x}
    (c : (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).X 3)
    (hsub : pointedTwoGenerator p - pointedTwoGenerator q =
      c ≫ (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 3 2) :
    pointedTwoHomologyClass p = pointedTwoHomologyClass q := by
  let K := X.normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let lp := pointedTwoCycle p
  let lq := pointedTwoCycle q
  have hlift : lp - lq =
      K.liftCycles (pointedTwoGenerator p - pointedTwoGenerator q) 1
        (by simp) (by
          rw [Preadditive.sub_comp, pointedTwoGenerator_cycle,
            pointedTwoGenerator_cycle, sub_zero]) := by
    apply (cancel_mono (K.iCycles 2)).mp
    rw [Preadditive.sub_comp]
    dsimp only [K, lp, lq]
    rw [pointedTwoCycle_i, pointedTwoCycle_i,
      HomologicalComplex.liftCycles_i]
  apply sub_eq_zero.mp
  change (lp ≫ K.homologyπ 2) - (lq ≫ K.homologyπ 2) = 0
  rw [← Preadditive.sub_comp, hlift]
  exact K.liftCycles_homologyπ_eq_zero_of_boundary
    (pointedTwoGenerator p - pointedTwoGenerator q) 1 (by simp) c
      (by simpa [K] using hsub)

/-- The signed boundary of a `RelStruct₀` filler is the difference of its
two pointed faces. -/
theorem pointedTwoGenerator_sub_eq_boundary_of_relStruct₀
    {X : SSet.{u}} {x : X _⦋0⦌} {p q : X.PtSimplex 2 x}
    (h : p.RelStruct₀ q) :
    pointedTwoGenerator p - pointedTwoGenerator q =
      X.ιNormalizedChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u}))
        (SSet.yonedaEquiv h.map) ≫
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 3 2 := by
  have hface0 : SSet.stdSimplex.δ (0 : Fin 4) ≫ h.map =
      RelativeMorphism.map p := by
    simpa using h.δ_castSucc_map
  have hface1 : SSet.stdSimplex.δ (Fin.succ 0 : Fin 4) ≫ h.map =
      RelativeMorphism.map q := by
    simpa using h.δ_succ_map
  have hf0 :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ 0 (SSet.yonedaEquiv h.map)) = pointedTwoGenerator p := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hface0]
    rfl
  have hf1 :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ (Fin.succ 0 : Fin 4) (SSet.yonedaEquiv h.map)) =
        pointedTwoGenerator q := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hface1]
    rfl
  have hf2 :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ (Fin.succ (Fin.succ 0) : Fin 4)
            (SSet.yonedaEquiv h.map)) = 0 := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp,
      h.δ_map_of_gt (Fin.succ (Fin.succ 0) : Fin 4) (by decide),
      ιNormalizedChainComplex_yonedaEquiv_const_eq_zero (n := 1)]
  have hf3 :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 4)
            (SSet.yonedaEquiv h.map)) = 0 := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp,
      h.δ_map_of_gt (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 4) (by decide),
      ιNormalizedChainComplex_yonedaEquiv_const_eq_zero (n := 1)]
  have hb := X.ιNormalizedChainComplex_d
    (R := (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})) (SSet.yonedaEquiv h.map)
  simp only [Fin.sum_univ_succ] at hb
  simp only [hf0, hf1, hf2, hf3] at hb
  exact (by simpa [sub_eq_add_neg] using hb.symm)

/-- Pointed two-simplices related by a native `RelStruct₀` filler determine
the same normalized homology class. -/
theorem pointedTwoHomologyClass_eq_of_relStruct₀
    {X : SSet.{u}} {x : X _⦋0⦌} {p q : X.PtSimplex 2 x}
    (h : p.RelStruct₀ q) :
    pointedTwoHomologyClass p = pointedTwoHomologyClass q :=
  pointedTwoHomologyClass_eq_of_sub_eq_boundary
    (X.ιNormalizedChainComplex
      (R := (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})) (SSet.yonedaEquiv h.map))
    (pointedTwoGenerator_sub_eq_boundary_of_relStruct₀ h)

/-- A boundary relation between three pointed generators becomes the
corresponding sum relation in normalized homology. -/
theorem pointedTwoHomologyClass_eq_add_of_sub_add_eq_boundary
    {X : SSet.{u}} {x : X _⦋0⦌} {p q r : X.PtSimplex 2 x}
    (c : (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u}) ⟶
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).X 3)
    (hsub : pointedTwoGenerator r -
        (pointedTwoGenerator p + pointedTwoGenerator q) =
      c ≫ (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 3 2) :
    pointedTwoHomologyClass r =
      pointedTwoHomologyClass p + pointedTwoHomologyClass q := by
  let K := X.normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let lr := pointedTwoCycle r
  let lp := pointedTwoCycle p
  let lq := pointedTwoCycle q
  have hlift : lr - (lp + lq) =
      K.liftCycles
        (pointedTwoGenerator r -
          (pointedTwoGenerator p + pointedTwoGenerator q))
        1 (by simp) (by
          rw [Preadditive.sub_comp, Preadditive.add_comp,
            pointedTwoGenerator_cycle r, pointedTwoGenerator_cycle p,
            pointedTwoGenerator_cycle q]
          simp) := by
    apply (cancel_mono (K.iCycles 2)).mp
    rw [Preadditive.sub_comp, Preadditive.add_comp]
    dsimp only [K, lr, lp, lq]
    rw [pointedTwoCycle_i, pointedTwoCycle_i, pointedTwoCycle_i,
      HomologicalComplex.liftCycles_i]
  apply sub_eq_zero.mp
  change (lr ≫ K.homologyπ 2) -
      ((lp ≫ K.homologyπ 2) + (lq ≫ K.homologyπ 2)) = 0
  rw [← Preadditive.add_comp, ← Preadditive.sub_comp, hlift]
  exact K.liftCycles_homologyπ_eq_zero_of_boundary
    (pointedTwoGenerator r -
      (pointedTwoGenerator p + pointedTwoGenerator q))
    1 (by simp) c (by simpa [K] using hsub)

/-- The signed boundary of a native product filler expresses the output
pointed generator as the sum of the two input generators, modulo a normalized
degree-three boundary. -/
theorem pointedTwoGenerator_sub_add_eq_boundary_of_mulStruct
    {X : SSet.{u}} {x : X _⦋0⦌} {p q r : X.PtSimplex 2 x}
    (h : p.MulStruct q r (Fin.last 1)) :
    pointedTwoGenerator r -
        (pointedTwoGenerator p + pointedTwoGenerator q) =
      X.ιNormalizedChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u}))
        (SSet.yonedaEquiv h.map) ≫
      (X.normalizedChainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 3 2 := by
  have hface0 : SSet.stdSimplex.δ (0 : Fin 4) ≫ h.map =
      SSet.const x :=
    h.δ_map_of_lt 0 (by decide)
  have hface1 : SSet.stdSimplex.δ (Fin.succ 0 : Fin 4) ≫ h.map =
      RelativeMorphism.map q := by
    simpa using h.δ_castSucc_castSucc_map
  have hface2 :
      SSet.stdSimplex.δ (Fin.succ (Fin.succ 0) : Fin 4) ≫ h.map =
        RelativeMorphism.map r := by
    simpa using h.δ_succ_castSucc_map
  have hface3 :
      SSet.stdSimplex.δ (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 4) ≫
          h.map = RelativeMorphism.map p := by
    simpa using h.δ_succ_succ_map
  have hf0 :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ 0 (SSet.yonedaEquiv h.map)) = 0 := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hface0,
      ιNormalizedChainComplex_yonedaEquiv_const_eq_zero (n := 1)]
  have hf1 :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ (Fin.succ 0 : Fin 4) (SSet.yonedaEquiv h.map)) =
        pointedTwoGenerator q := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hface1]
    rfl
  have hf2 :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ (Fin.succ (Fin.succ 0) : Fin 4)
            (SSet.yonedaEquiv h.map)) = pointedTwoGenerator r := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hface2]
    rfl
  have hf3 :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 4)
            (SSet.yonedaEquiv h.map)) = pointedTwoGenerator p := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hface3]
    rfl
  have hfaces (i : Fin 4) :
      X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ i (SSet.yonedaEquiv h.map)) =
        if i = 0 then 0
        else if i = 1 then pointedTwoGenerator q
        else if i = 2 then pointedTwoGenerator r
        else pointedTwoGenerator p := by
    fin_cases i
    · simpa using hf0
    · simpa using hf1
    · simpa using hf2
    · simpa using hf3
  have hb := X.ιNormalizedChainComplex_d
    (R := (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})) (SSet.yonedaEquiv h.map)
  have hsum :
      (∑ i : Fin 4, (-1) ^ i.val •
        X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ i (SSet.yonedaEquiv h.map))) =
        -pointedTwoGenerator q +
          (pointedTwoGenerator r + -pointedTwoGenerator p) := by
    simp_rw [hfaces]
    simp [Fin.sum_univ_succ]
  calc
    _ = -pointedTwoGenerator q +
        (pointedTwoGenerator r + -pointedTwoGenerator p) := by abel
    _ = ∑ i : Fin 4, (-1) ^ i.val •
        X.ιNormalizedChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}))
          (X.δ i (SSet.yonedaEquiv h.map)) := hsum.symm
    _ = _ := hb.symm

/-- A native product filler sends the output pointed simplex to the sum of
the two input normalized homology classes. -/
theorem pointedTwoHomologyClass_mulStruct
    {X : SSet.{u}} {x : X _⦋0⦌} {p q r : X.PtSimplex 2 x}
    (h : p.MulStruct q r (Fin.last 1)) :
    pointedTwoHomologyClass r =
      pointedTwoHomologyClass p + pointedTwoHomologyClass q :=
  pointedTwoHomologyClass_eq_add_of_sub_add_eq_boundary
    (X.ιNormalizedChainComplex
      (R := (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})) (SSet.yonedaEquiv h.map))
    (pointedTwoGenerator_sub_add_eq_boundary_of_mulStruct h)

/-- The constant pointed two-simplex has zero normalized generator. -/
theorem pointedTwoGenerator_const
    {X : SSet.{u}} (x : X _⦋0⦌) :
    pointedTwoGenerator (RelativeMorphism.const : X.PtSimplex 2 x) = 0 := by
  change X.ιNormalizedChainComplex
      (R := (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u}))
      (SSet.yonedaEquiv (SSet.const x : Δ[2] ⟶ X)) = 0
  exact ιNormalizedChainComplex_yonedaEquiv_const_eq_zero 1 x

/-- The constant pointed two-simplex gives the zero normalized cycle. -/
theorem pointedTwoCycle_const
    {X : SSet.{u}} (x : X _⦋0⦌) :
    pointedTwoCycle (RelativeMorphism.const : X.PtSimplex 2 x) = 0 := by
  let K := X.normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  apply (cancel_mono (K.iCycles 2)).mp
  rw [pointedTwoCycle_i, zero_comp, pointedTwoGenerator_const]

/-- The constant pointed two-simplex gives the zero normalized homology
class. -/
theorem pointedTwoHomologyClass_const
    {X : SSet.{u}} (x : X _⦋0⦌) :
    pointedTwoHomologyClass
      (RelativeMorphism.const : X.PtSimplex 2 x) = 0 := by
  rw [pointedTwoHomologyClass, pointedTwoCycle_const, zero_comp]

/-- The representative-level degree-two Hurewicz function. -/
noncomputable def degreeTwoHurewiczFn
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌) :
    SSet.KanComplex.π 2 X x →
      ((AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u}) ⟶
        (X.normalizedChainComplex
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).homology 2) :=
  Quot.lift pointedTwoHomologyClass (by
    rintro p q ⟨h⟩
    exact pointedTwoHomologyClass_eq_of_relStruct₀
      (SSet.PtSimplex.Homotopy.relStruct₀ h))

/-- The degree-two Hurewicz function sends a native representative to its
normalized pointed-simplex class. -/
@[simp]
theorem degreeTwoHurewiczFn_mk
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌)
    (p : X.PtSimplex 2 x) :
    degreeTwoHurewiczFn x (SSet.KanComplex.π.mk p) =
      pointedTwoHomologyClass p :=
  rfl

/-- The degree-two Hurewicz function preserves the unit. -/
theorem degreeTwoHurewiczFn_one
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌) :
    degreeTwoHurewiczFn x 1 = 0 := by
  change pointedTwoHomologyClass
      (RelativeMorphism.const : X.PtSimplex 2 x) = 0
  exact pointedTwoHomologyClass_const x

/-- The degree-two Hurewicz function sends the native product to addition of
normalized homology classes. -/
theorem degreeTwoHurewiczFn_mul
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌)
    (a b : SSet.KanComplex.π 2 X x) :
    degreeTwoHurewiczFn x (a * b) =
      degreeTwoHurewiczFn x a + degreeTwoHurewiczFn x b := by
  induction a using SSet.KanComplex.π.rec with
  | mk p =>
    induction b using SSet.KanComplex.π.rec with
    | mk q =>
      obtain ⟨r, ⟨h⟩⟩ :=
        SSet.PtSimplex.MulStruct.nonempty p q (Fin.last 1)
      rw [h.mul_eq]
      simp only [degreeTwoHurewiczFn_mk]
      exact pointedTwoHomologyClass_mulStruct h

/-- The native degree-two Hurewicz homomorphism, with the additive target
written multiplicatively. -/
noncomputable def degreeTwoHurewiczMulHom
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌) :
    SSet.KanComplex.π 2 X x →*
      Multiplicative
        ((AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}) ⟶
          (X.normalizedChainComplex
            (AlgebraicTopology.singularIntegralCoefficients :
              AddCommGrpCat.{u})).homology 2) where
  toFun a := Multiplicative.ofAdd (degreeTwoHurewiczFn x a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change degreeTwoHurewiczFn x
      (SSet.KanComplex.π.group (n := 1) (X := X) (x := x)).one = 0
    rw [SSet.KanComplex.π.group_one_eq_instOne]
    exact degreeTwoHurewiczFn_one x
  map_mul' a b := degreeTwoHurewiczFn_mul x a b

/-- Exact representative formula for the native degree-two Hurewicz
homomorphism. -/
@[simp]
theorem degreeTwoHurewiczMulHom_mk
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌)
    (p : X.PtSimplex 2 x) :
    degreeTwoHurewiczMulHom x (SSet.KanComplex.π.mk p) =
      Multiplicative.ofAdd (pointedTwoHomologyClass p) :=
  rfl

/-- Evaluation at the positive integral generator turns the morphism-valued
Hurewicz homomorphism into the underlying-element-valued homomorphism. -/
noncomputable def degreeTwoHurewiczElementMulHom
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌) :
    SSet.KanComplex.π 2 X x →*
      Multiplicative
        ((X.normalizedChainComplex
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).homology 2) where
  toFun a := Multiplicative.ofAdd
    (degreeTwoHurewiczFn x a (ULift.up 1))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change degreeTwoHurewiczFn x
      (SSet.KanComplex.π.group (n := 1) (X := X) (x := x)).one
        (ULift.up 1) = 0
    rw [SSet.KanComplex.π.group_one_eq_instOne]
    change pointedTwoHomologyClass
      (RelativeMorphism.const : X.PtSimplex 2 x) (ULift.up 1) = 0
    rw [pointedTwoHomologyClass_const]
    rfl
  map_mul' a b := by
    rw [degreeTwoHurewiczFn_mul]
    rfl

/-- Exact representative formula for the element-valued Hurewicz
homomorphism. -/
@[simp]
theorem degreeTwoHurewiczElementMulHom_mk
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌)
    (p : X.PtSimplex 2 x) :
    degreeTwoHurewiczElementMulHom x (SSet.KanComplex.π.mk p) =
      Multiplicative.ofAdd (pointedTwoHomologyClass p (ULift.up 1)) :=
  rfl

/-- Naturality of the normalized pointed two-generator under a pointed
simplicial map. -/
theorem pointedTwoGenerator_map
    {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X ⟶ Y) (hxy : f.app _ x = y) (p : X.PtSimplex 2 x) :
    pointedTwoGenerator p ≫
        (SSet.normalizedChainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).f 2 =
      pointedTwoGenerator (SSet.PtSimplex.map f hxy p) := by
  rw [pointedTwoGenerator, SSet.ι_normalizedChainComplexMap_f]
  rfl

/-- Naturality of the normalized pointed two-cycle. -/
theorem pointedTwoCycle_map
    {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X ⟶ Y) (hxy : f.app _ x = y) (p : X.PtSimplex 2 x) :
    pointedTwoCycle p ≫
        HomologicalComplex.cyclesMap
          (SSet.normalizedChainComplexMap f
            (AlgebraicTopology.singularIntegralCoefficients :
              AddCommGrpCat.{u})) 2 =
      pointedTwoCycle (SSet.PtSimplex.map f hxy p) := by
  let KX := X.normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let KY := Y.normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let φ := SSet.normalizedChainComplexMap f
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  apply (cancel_mono (KY.iCycles 2)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, pointedTwoCycle_i, pointedTwoCycle_i]
  exact pointedTwoGenerator_map f hxy p

/-- Naturality of the normalized homology class represented by a pointed
two-simplex. -/
theorem pointedTwoHomologyClass_map
    {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X ⟶ Y) (hxy : f.app _ x = y) (p : X.PtSimplex 2 x) :
    pointedTwoHomologyClass p ≫
        HomologicalComplex.homologyMap
          (SSet.normalizedChainComplexMap f
            (AlgebraicTopology.singularIntegralCoefficients :
              AddCommGrpCat.{u})) 2 =
      pointedTwoHomologyClass (SSet.PtSimplex.map f hxy p) := by
  rw [pointedTwoHomologyClass, Category.assoc,
    HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, pointedTwoCycle_map]
  rfl

/-- Representative-level naturality of the native degree-two Hurewicz map
under a pointed simplicial map. -/
theorem degreeTwoHurewiczFn_naturality
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X ⟶ Y) (hxy : f.app _ x = y)
    (a : SSet.KanComplex.π 2 X x) :
    degreeTwoHurewiczFn y (SSet.KanComplex.π.map f hxy 2 a) =
      degreeTwoHurewiczFn x a ≫
        HomologicalComplex.homologyMap
          (SSet.normalizedChainComplexMap f
            (AlgebraicTopology.singularIntegralCoefficients :
              AddCommGrpCat.{u})) 2 := by
  induction a using SSet.KanComplex.π.rec with
  | mk p =>
    simp only [SSet.KanComplex.π.map_mk, degreeTwoHurewiczFn_mk]
    exact (pointedTwoHomologyClass_map f hxy p).symm

end SSet
