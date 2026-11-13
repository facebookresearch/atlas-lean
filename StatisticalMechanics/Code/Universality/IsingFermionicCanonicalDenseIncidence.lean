/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge
import Code.Universality.IsingFermionicPhysicalFullSquareIncidence
import Code.Universality.IsingFermionicTensorTentMorera











open Filter Set Topology

namespace StatMech.Universality

noncomputable section


def fkIsingRationalComplex (q : Rat × Rat) : Complex :=
  (q.1 : Real) + (q.2 : Real) * Complex.I

theorem fkIsingRationalComplex_denseRange :
    DenseRange fkIsingRationalComplex := by
  let realPair : Rat × Rat → Real × Real :=
    Prod.map ((↑) : Rat → Real) ((↑) : Rat → Real)
  let toComplex : Real × Real → Complex := fun p ↦
    p.1 + p.2 * Complex.I
  have hpair : DenseRange realPair :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hsurj : Function.Surjective toComplex := by
    intro z
    refine ⟨(z.re, z.im), ?_⟩
    apply Complex.ext <;> simp [toComplex]
  have hcontinuous : Continuous toComplex := by
    unfold toComplex
    fun_prop
  have hcomp := hsurj.denseRange.comp hpair hcontinuous
  simpa only [Function.comp_def, realPair, toComplex,
    fkIsingRationalComplex, Prod.map_apply] using hcomp


noncomputable def fkIsingRationalPairEnumeration : Nat → Rat × Rat :=
  Classical.choose (exists_surjective_nat (Rat × Rat))

theorem fkIsingRationalPairEnumeration_surjective :
    Function.Surjective fkIsingRationalPairEnumeration :=
  Classical.choose_spec (exists_surjective_nat (Rat × Rat))


noncomputable def fkIsingDenseRationalPoint (j : Nat) : Complex :=
  fkIsingRationalComplex (fkIsingRationalPairEnumeration j)

theorem fkIsingDenseRationalPoint_denseRange :
    DenseRange fkIsingDenseRationalPoint := by
  have henum : DenseRange fkIsingRationalPairEnumeration :=
    fkIsingRationalPairEnumeration_surjective.denseRange
  have hcontinuous : Continuous fkIsingRationalComplex := by
    unfold fkIsingRationalComplex
    fun_prop
  simpa only [Function.comp_def, fkIsingDenseRationalPoint] using
    fkIsingRationalComplex_denseRange.comp henum hcontinuous

private theorem int_natAbs_le_iff (x : Int) (n : Nat) :
    x.natAbs ≤ n ↔ -(n : Int) ≤ x ∧ x ≤ n := by
  rw [show x.natAbs ≤ n ↔ |x| ≤ (n : Int) by
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_le.symm]
  exact abs_le



def fkIsingSquareFullVertexOfInt
    (n : Nat) (x y : Int)
    (hx : -(n : Int) ≤ x ∧ x ≤ n)
    (hy : -(n : Int) ≤ y ∧ y ≤ n) :
    FKIsingSquareFullVertexNode n := by
  refine ⟨![x, y], ?_⟩
  intro i
  fin_cases i
  · exact (int_natAbs_le_iff x n).2 hx
  · exact (int_natAbs_le_iff y n).2 hy



noncomputable def fkIsingSquareInteriorRadialIncidenceOfInt
    (n : Nat) (hn : 0 < n) (x y : Int)
    (hxy : -(n : Int) ≤ x ∧ x < n ∧
      -(n : Int) ≤ y ∧ y < n) :
    FKIsingSquareInteriorRadialIncidence n hn := by
  let v : FKIsingSquareFullVertexNode n :=
    fkIsingSquareFullVertexOfInt n x y
      ⟨hxy.1, le_of_lt hxy.2.1⟩
      ⟨hxy.2.2.1, le_of_lt hxy.2.2.2⟩
  have hp : fkIsingSquareInteriorFaceKey n (x, y) := by
    simpa [fkIsingSquareInteriorFaceKey] using hxy
  let c : FKIsingSquareFullFaceNode n :=
    fkIsingSquareFullFaceOfKey n (x, y) hp
  have hadj : FKIsingSquareFullRadiallyAdjacent n v c := by
    left
    simp [v, c, fkIsingSquareFullFaceCoordinate,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareFullVertexOfInt]
  exact fkIsingSquareFullIncidenceOfAdjacent n hn v c hadj

@[simp] theorem fkIsingSquareInteriorRadialIncidenceOfInt_endpoint
    (n : Nat) (hn : 0 < n) (x y : Int)
    (hxy : -(n : Int) ≤ x ∧ x < n ∧
      -(n : Int) ≤ y ∧ y < n) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareInteriorRadialIncidenceOfInt n hn x y hxy) =
      fkIsingSquareFullVertexOfInt n x y
        ⟨hxy.1, le_of_lt hxy.2.1⟩
        ⟨hxy.2.2.1, le_of_lt hxy.2.2.2⟩ := by
  simp [fkIsingSquareInteriorRadialIncidenceOfInt]


theorem fullSquareScaledVertexEmbedding_fullVertexOfInt
    (n : Nat) (scale : Real) (x y : Int)
    (hx : -(n : Int) ≤ x ∧ x ≤ n)
    (hy : -(n : Int) ≤ y ∧ y ≤ n) :
    FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding
        n scale (fkIsingSquareFullVertexOfInt n x y hx hy) =
      (scale : Complex) *
        (((x + y : Int) : Real) + ((x - y : Int) : Real) * Complex.I) := by
  simp [FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding,
    FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledCoordinateEmbedding,
    fkIsingSquareFullVertexCoordinate, fkIsingSquareFullVertexOfInt,
    fkIsingSquareWiredIntPoint, Algebra.smul_def]



def fkIsingDenseRationalPrimalX (q : Rat × Rat) (k : Nat) : Int :=
  ⌊(((q.1 : Real) + (q.2 : Real)) / 2) * (k + 1 : Real)⌋

def fkIsingDenseRationalPrimalY (q : Rat × Rat) (k : Nat) : Int :=
  ⌊(((q.1 : Real) - (q.2 : Real)) / 2) * (k + 1 : Real)⌋



theorem fkIsing_floor_mul_succ_eventually_in_expandingSquare (c : Real) :
    ∀ᶠ k : Nat in atTop,
      -(fkIsingExpandingSquareSide k : Int) ≤ ⌊c * (k + 1 : Real)⌋ ∧
        ⌊c * (k + 1 : Real)⌋ < fkIsingExpandingSquareSide k := by
  obtain ⟨M : Nat, hM⟩ := exists_nat_ge |c|
  filter_upwards [eventually_ge_atTop (M + 1)] with k hk
  have ht : (M : Real) + 1 < (k + 1 : Real) := by
    exact_mod_cast (show M + 1 < k + 1 by omega)
  have htpos : 0 < (k + 1 : Real) := by positivity
  have hcUpper : c ≤ M := le_trans (le_abs_self c) hM
  have hcLower : -(M : Real) ≤ c := by
    exact le_trans (neg_le_neg hM) (neg_abs_le c)
  constructor
  · have hfloorLower :
        (-(fkIsingExpandingSquareSide k : Int) : Int) <
          ⌊c * (k + 1 : Real)⌋ := by
      have hside : (fkIsingExpandingSquareSide k : Real) =
          (k + 1 : Real) ^ 2 := by
        norm_num [fkIsingExpandingSquareSide]
      have hreal :
          -(fkIsingExpandingSquareSide k : Real) <
            ((⌊c * (k + 1 : Real)⌋ : Int) : Real) := by
        calc
          -(fkIsingExpandingSquareSide k : Real) <
              c * (k + 1 : Real) - 1 := by
                rw [hside]
                nlinarith
          _ < ((⌊c * (k + 1 : Real)⌋ : Int) : Real) :=
            Int.sub_one_lt_floor _
      exact_mod_cast hreal
    omega
  · rw [Int.floor_lt]
    have hside : (fkIsingExpandingSquareSide k : Real) =
        (k + 1 : Real) ^ 2 := by
      norm_num [fkIsingExpandingSquareSide]
    norm_cast
    rw [hside]
    push_cast
    nlinarith



theorem fkIsingDenseRationalPrimal_eventually_interior (q : Rat × Rat) :
    ∀ᶠ k : Nat in atTop,
      -(fkIsingExpandingSquareSide k : Int) ≤
          fkIsingDenseRationalPrimalX q k ∧
        fkIsingDenseRationalPrimalX q k < fkIsingExpandingSquareSide k ∧
      -(fkIsingExpandingSquareSide k : Int) ≤
          fkIsingDenseRationalPrimalY q k ∧
        fkIsingDenseRationalPrimalY q k < fkIsingExpandingSquareSide k := by
  filter_upwards
    [fkIsing_floor_mul_succ_eventually_in_expandingSquare
      (((q.1 : Real) + (q.2 : Real)) / 2),
     fkIsing_floor_mul_succ_eventually_in_expandingSquare
      (((q.1 : Real) - (q.2 : Real)) / 2)] with k hx hy
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩




noncomputable def fkIsingDenseRationalIncidence
    (q : Rat × Rat) (k : Nat) :
    FKIsingSquareInteriorRadialIncidence
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) := by
  let x := fkIsingDenseRationalPrimalX q k
  let y := fkIsingDenseRationalPrimalY q k
  if h : -(fkIsingExpandingSquareSide k : Int) ≤ x ∧
      x < fkIsingExpandingSquareSide k ∧
      -(fkIsingExpandingSquareSide k : Int) ≤ y ∧
      y < fkIsingExpandingSquareSide k then
    exact fkIsingSquareInteriorRadialIncidenceOfInt
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      x y h
  else
    exact fkIsingSquareInteriorRadialIncidenceOfInt
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      0 0 (by
        have hn := fkIsingExpandingSquareSide_pos k
        constructor
        · omega
        constructor
        · exact_mod_cast hn
        constructor
        · omega
        · exact_mod_cast hn)



theorem fkIsingExpandingSquareScale_mul_floor_succ_tendsto (c : Real) :
    Tendsto
      (fun k ↦ fkIsingExpandingSquareScale k *
        ((⌊c * (k + 1 : Real)⌋ : Int) : Real))
      atTop (nhds c) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hscale := (Metric.tendsto_nhds.1
    fkIsingExpandingSquareScale_tendsto_zero) epsilon hepsilon
  filter_upwards [hscale] with k hk
  rw [Real.dist_eq]
  have hspos : 0 < fkIsingExpandingSquareScale k :=
    fkIsingExpandingSquareScale_pos k
  have hscaleSucc :
      fkIsingExpandingSquareScale k * (k + 1 : Real) = 1 := by
    simp only [fkIsingExpandingSquareScale, one_div]
    push_cast
    exact inv_mul_cancel₀ (show (k : Real) + 1 ≠ 0 by positivity)
  have hupper :
      fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) ≤ c := by
    have hfloor := Int.floor_le (c * (k + 1 : Real))
    have hmul := mul_le_mul_of_nonneg_left hfloor hspos.le
    calc
      fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) ≤
          fkIsingExpandingSquareScale k * (c * (k + 1 : Real)) := hmul
      _ = c * (fkIsingExpandingSquareScale k * (k + 1 : Real)) := by ring
      _ = c := by rw [hscaleSucc, mul_one]
  have hlower :
      c - fkIsingExpandingSquareScale k <
        fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) := by
    have hfloor := Int.sub_one_lt_floor (c * (k + 1 : Real))
    have hmul := mul_lt_mul_of_pos_left hfloor hspos
    calc
      c - fkIsingExpandingSquareScale k =
          fkIsingExpandingSquareScale k *
            (c * (k + 1 : Real) - 1) := by
              rw [mul_sub, mul_one]
              calc
                c - fkIsingExpandingSquareScale k =
                    c * (fkIsingExpandingSquareScale k * (k + 1 : Real)) -
                      fkIsingExpandingSquareScale k := by rw [hscaleSucc, mul_one]
                _ = fkIsingExpandingSquareScale k * (c * (k + 1 : Real)) -
                      fkIsingExpandingSquareScale k := by ring
      _ < fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) := hmul
  have hnonpos :
      fkIsingExpandingSquareScale k *
          ((⌊c * (k + 1 : Real)⌋ : Int) : Real) - c ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  have hk' : fkIsingExpandingSquareScale k < epsilon := by
    simpa [Real.dist_eq, abs_of_pos hspos] using hk
  linarith



theorem fkIsingDenseRationalIncidence_embedding_tendsto (q : Rat × Rat) :
    Tendsto
      (fun k ↦
        FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
          (fkIsingSquareInteriorRadialEndpoint
            (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
            (fkIsingDenseRationalIncidence q k)))
      atTop (nhds (fkIsingRationalComplex q)) := by
  let cx : Real := ((q.1 : Real) + (q.2 : Real)) / 2
  let cy : Real := ((q.1 : Real) - (q.2 : Real)) / 2
  let x : Nat → Int := fun k ↦ ⌊cx * (k + 1 : Real)⌋
  let y : Nat → Int := fun k ↦ ⌊cy * (k + 1 : Real)⌋
  have hx : Tendsto
      (fun k ↦ fkIsingExpandingSquareScale k * ((x k : Int) : Real))
      atTop (nhds cx) := by
    simpa [x] using fkIsingExpandingSquareScale_mul_floor_succ_tendsto cx
  have hy : Tendsto
      (fun k ↦ fkIsingExpandingSquareScale k * ((y k : Int) : Real))
      atTop (nhds cy) := by
    simpa [y] using fkIsingExpandingSquareScale_mul_floor_succ_tendsto cy
  have hre := hx.add hy
  have him := hx.sub hy
  have hreComplex := (Complex.continuous_ofReal.tendsto (cx + cy)).comp hre
  have himComplex := (Complex.continuous_ofReal.tendsto (cx - cy)).comp him
  have hformula := hreComplex.add (himComplex.mul_const Complex.I)
  have htarget :
      ((cx + cy : Real) : Complex) +
          ((cx - cy : Real) : Complex) * Complex.I =
        fkIsingRationalComplex q := by
    simp [fkIsingRationalComplex, cx, cy]
    ring
  have hformula' : Tendsto
      (fun k ↦
        ((fkIsingExpandingSquareScale k * ((x k : Int) : Real) +
            fkIsingExpandingSquareScale k * ((y k : Int) : Real) : Real) :
          Complex) +
        ((fkIsingExpandingSquareScale k * ((x k : Int) : Real) -
            fkIsingExpandingSquareScale k * ((y k : Int) : Real) : Real) :
          Complex) * Complex.I)
      atTop (nhds (fkIsingRationalComplex q)) := by
    rw [← htarget]
    simpa only [Function.comp_apply] using hformula
  apply hformula'.congr'
  filter_upwards [fkIsingDenseRationalPrimal_eventually_interior q]
    with k hk
  have hxDef : x k = fkIsingDenseRationalPrimalX q k := by
    rfl
  have hyDef : y k = fkIsingDenseRationalPrimalY q k := by
    rfl
  rw [show fkIsingDenseRationalIncidence q k =
      fkIsingSquareInteriorRadialIncidenceOfInt
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (x k) (y k) (by simpa [hxDef, hyDef] using hk) by
    simp [fkIsingDenseRationalIncidence, hxDef, hyDef, hk]]
  rw [fkIsingSquareInteriorRadialIncidenceOfInt_endpoint]
  rw [fullSquareScaledVertexEmbedding_fullVertexOfInt]
  simp [Complex.ext_iff]
  constructor <;> ring




noncomputable def fkIsingExpandingSquareDenseIncidenceFamily :
    FKIsingDenseIncidenceFamily
      fkIsingExpandingSquareSide fkIsingExpandingSquareSide_pos
      fkIsingExpandingSquareScale where
  point := fkIsingDenseRationalPoint
  incidence j k :=
    fkIsingDenseRationalIncidence (fkIsingRationalPairEnumeration j) k
  embedding_tendsto j := by
    exact fkIsingDenseRationalIncidence_embedding_tendsto
      (fkIsingRationalPairEnumeration j)
  dense_range := fkIsingDenseRationalPoint_denseRange


def FKIsingDenseRationalInterior (q : Rat × Rat) (k : Nat) : Prop :=
  -(fkIsingExpandingSquareSide k : Int) ≤
      fkIsingDenseRationalPrimalX q k ∧
    fkIsingDenseRationalPrimalX q k < fkIsingExpandingSquareSide k ∧
  -(fkIsingExpandingSquareSide k : Int) ≤
      fkIsingDenseRationalPrimalY q k ∧
    fkIsingDenseRationalPrimalY q k < fkIsingExpandingSquareSide k



noncomputable def fkIsingDenseRationalPathX (q : Rat × Rat) (k : Nat) : Int := by
  classical
  exact if FKIsingDenseRationalInterior q k then
      fkIsingDenseRationalPrimalX q k else 0

noncomputable def fkIsingDenseRationalPathY (q : Rat × Rat) (k : Nat) : Int := by
  classical
  exact if FKIsingDenseRationalInterior q k then
      fkIsingDenseRationalPrimalY q k else 0



def fkIsingDenseRationalPathSteps (q : Rat × Rat) (k : Nat) : Nat :=
  (fkIsingDenseRationalPathX q k).natAbs +
    (fkIsingDenseRationalPathY q k).natAbs


theorem fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le
    (c : Real) (k : Nat) :
    fkIsingExpandingSquareScale k *
        (⌊c * (k + 1 : Real)⌋ : Int).natAbs ≤ |c| + 1 := by
  let z : Int := ⌊c * (k + 1 : Real)⌋
  have hzUpper : (z : Real) ≤ c * (k + 1 : Real) := Int.floor_le _
  have hzLower : c * (k + 1 : Real) - 1 < (z : Real) :=
    Int.sub_one_lt_floor _
  have hzAbs : |(z : Real)| ≤ |c * (k + 1 : Real)| + 1 := by
    rw [abs_le]
    constructor <;>
      nlinarith [neg_abs_le (c * (k + 1 : Real)),
        le_abs_self (c * (k + 1 : Real))]
  have hspos : 0 < fkIsingExpandingSquareScale k :=
    fkIsingExpandingSquareScale_pos k
  have hscaleSucc :
      fkIsingExpandingSquareScale k * (k + 1 : Real) = 1 := by
    simp only [fkIsingExpandingSquareScale, one_div]
    push_cast
    exact inv_mul_cancel₀ (show (k : Real) + 1 ≠ 0 by positivity)
  have hsle : fkIsingExpandingSquareScale k ≤ 1 := by
    have ht : (1 : Real) ≤ k + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith
  calc
    fkIsingExpandingSquareScale k * (z.natAbs : Real) =
        fkIsingExpandingSquareScale k * |(z : Real)| := by
          simp only [Nat.cast_natAbs, Int.cast_abs]
    _ ≤ fkIsingExpandingSquareScale k *
        (|c * (k + 1 : Real)| + 1) :=
      mul_le_mul_of_nonneg_left hzAbs hspos.le
    _ = |c| + fkIsingExpandingSquareScale k := by
      rw [mul_add, mul_one, abs_mul, abs_of_pos (by positivity :
        (0 : Real) < k + 1)]
      calc
        fkIsingExpandingSquareScale k * (|c| * (k + 1 : Real)) +
            fkIsingExpandingSquareScale k =
          |c| * (fkIsingExpandingSquareScale k * (k + 1 : Real)) +
            fkIsingExpandingSquareScale k := by ring
        _ = |c| + fkIsingExpandingSquareScale k := by rw [hscaleSucc, mul_one]
    _ ≤ |c| + 1 := by simpa [add_comm] using add_le_add_left hsle |c|



theorem fkIsingDenseRationalPath_length_le (q : Rat × Rat) (k : Nat) :
    (fkIsingDenseRationalPathSteps q k : Real) *
        (2 * fkIsingExpandingSquareScale k) ≤
      2 *
        (|((q.1 : Real) + (q.2 : Real)) / 2| +
          |((q.1 : Real) - (q.2 : Real)) / 2| + 2) := by
  let cx : Real := ((q.1 : Real) + (q.2 : Real)) / 2
  let cy : Real := ((q.1 : Real) - (q.2 : Real)) / 2
  have hxRaw :=
    fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le cx k
  have hyRaw :=
    fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le cy k
  have hx : fkIsingExpandingSquareScale k *
      (fkIsingDenseRationalPathX q k).natAbs ≤ |cx| + 1 := by
    by_cases h : FKIsingDenseRationalInterior q k
    · simpa [fkIsingDenseRationalPathX, h, fkIsingDenseRationalPrimalX,
        cx] using hxRaw
    · simp only [fkIsingDenseRationalPathX, h, if_false,
        Int.natAbs_zero, Nat.cast_zero, mul_zero]
      positivity
  have hy : fkIsingExpandingSquareScale k *
      (fkIsingDenseRationalPathY q k).natAbs ≤ |cy| + 1 := by
    by_cases h : FKIsingDenseRationalInterior q k
    · simpa [fkIsingDenseRationalPathY, h, fkIsingDenseRationalPrimalY,
        cy] using hyRaw
    · simp only [fkIsingDenseRationalPathY, h, if_false,
        Int.natAbs_zero, Nat.cast_zero, mul_zero]
      positivity
  dsimp [fkIsingDenseRationalPathSteps]
  push_cast
  dsimp [cx, cy] at hx hy ⊢
  nlinarith [fkIsingExpandingSquareScale_pos k]




structure FKIsingCanonicalDensePrimitiveLocalInputs
    (F : Nat → Complex → Complex) where
  canonicalPath : Nat → Nat → Nat → Real
  discretePath : Nat → Nat → Nat → Real
  error : Nat → Nat → Real
  canonical_endpoint : ∀ j k,
    canonicalPath j k
        (fkIsingDenseRationalPathSteps
          (fkIsingRationalPairEnumeration j) k) =
      (isingFermionicEntireSquarePrimitive
        (F k) (fkIsingDenseRationalPoint j)).im
  discrete_endpoint : ∀ j k,
    discretePath j k
        (fkIsingDenseRationalPathSteps
          (fkIsingRationalPairEnumeration j) k) =
      fkIsingExpandingSquareDenseIncidenceFamily.discreteVertexPrimitive j k
  base_tendsto : ∀ j, Tendsto
    (fun k ↦ canonicalPath j k 0 - discretePath j k 0)
    atTop (nhds 0)
  error_tendsto : ∀ j, Tendsto (error j) atTop (nhds 0)
  error_nonneg : ∀ j k, 0 ≤ error j k
  increment_error : ∀ j k i,
    i < fkIsingDenseRationalPathSteps
        (fkIsingRationalPairEnumeration j) k →
      abs ((canonicalPath j k (i + 1) - canonicalPath j k i) -
        (discretePath j k (i + 1) - discretePath j k i)) ≤
          (2 * fkIsingExpandingSquareScale k) * error j k

namespace FKIsingCanonicalDensePrimitiveLocalInputs



noncomputable def toPathCompatibility
    {F : Nat → Complex → Complex}
    (L : FKIsingCanonicalDensePrimitiveLocalInputs F) :
    FKIsingDenseIncidencePrimitivePathCompatibility
      (N := fkIsingExpandingSquareSide)
      (hN := fkIsingExpandingSquareSide_pos)
      (mesh := fkIsingExpandingSquareScale) F
      fkIsingExpandingSquareDenseIncidenceFamily where
  steps j k := fkIsingDenseRationalPathSteps
    (fkIsingRationalPairEnumeration j) k
  stepLength _ k := 2 * fkIsingExpandingSquareScale k
  error := L.error
  pathBound j := 2 *
    (|(((fkIsingRationalPairEnumeration j).1 : Real) +
          ((fkIsingRationalPairEnumeration j).2 : Real)) / 2| +
      |(((fkIsingRationalPairEnumeration j).1 : Real) -
          ((fkIsingRationalPairEnumeration j).2 : Real)) / 2| + 2)
  canonicalPath := L.canonicalPath
  discretePath := L.discretePath
  canonical_endpoint := L.canonical_endpoint
  discrete_endpoint := L.discrete_endpoint
  base_tendsto := L.base_tendsto
  error_tendsto := L.error_tendsto
  error_nonneg := L.error_nonneg
  pathBound_nonneg j := by positivity
  path_length_le j k := by
    exact fkIsingDenseRationalPath_length_le
      (fkIsingRationalPairEnumeration j) k
  increment_error := L.increment_error

end FKIsingCanonicalDensePrimitiveLocalInputs

end

end StatMech.Universality
