/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Actual code-word addition in the Leech quotient, including the integral XOR
carry. Source: Seysen, arXiv:2002.10921v3, proof of Theorem 6.1.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerThetaAddition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Integral characteristic vector of a code word. -/
def sourceCodeInteger (d : Fin 4096) (i : Fin 24) : ℤ :=
  if (golayEncodedMask d.val).testBit i.val then 1 else 0

/-- The intersection that supplies the cocode correction to code addition. -/
def sourceCodeIntersection (d e : Fin 4096) (i : Fin 24) : ℤ :=
  sourceCodeInteger d i * sourceCodeInteger e i

/-- Code weights are multiples of four, including the all-one word. -/
theorem sourceCodeInteger_sum (d : Fin 4096) :
    ∑ i, sourceCodeInteger d i = 4 * (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  have h : (∑ i, sourceCodeInteger d i) =
      (golayMaskWeight (golayEncodedMask d.val) : ℤ) := by
    simp only [sourceCodeInteger, golayMaskWeight, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num
  rw [h]
  have hw := golayEncodedMask_weights d
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | hw | hw | hw | hw <;> rw [hw] <;> norm_num

/-- The integer carry for XOR follows from linearity of the actual Golay encoder. -/
theorem sourceCodeInteger_add (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e)
    (i : Fin 24) :
    sourceCodeInteger d i + sourceCodeInteger e i - sourceCodeInteger f i =
      2 * sourceCodeIntersection d e i := by
  have h := congrFun (congrArg golayEncoder hf) i
  rw [map_add, Pi.add_apply] at h
  have hv : ∀ a : Fin 4096,
      golayEncoder (golayLabelCoefficients a) i =
        if (golayEncodedMask a.val).testBit i.val then 1 else 0 := by
    intro a
    apply ZMod.val_injective
    cases hb : (golayEncodedMask a.val).testBit i.val <;>
      simpa [hb, show (1 : ZMod 2).val = 1 by decide] using golayLabelEncoder_match a i
  simp_rw [hv] at h
  cases hd : (golayEncodedMask d.val).testBit i.val <;>
    cases he : (golayEncodedMask e.val).testBit i.val <;>
    cases hf' : (golayEncodedMask f.val).testBit i.val <;>
    simp_all [sourceCodeInteger, sourceCodeIntersection]

/-- Summing the XOR carry gives the weight identity used in the source proof. -/
theorem sourceCodeIntersection_sum (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    ∑ i, sourceCodeIntersection d e i =
      2 * ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
        (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) -
        (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) : ℤ) := by
  have h := congrArg (fun v : Fin 24 → ℤ => ∑ i, v i)
    (funext (sourceCodeInteger_add d e f hf))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [sourceCodeInteger_sum, sourceCodeInteger_sum, sourceCodeInteger_sum] at h
  linarith

/-- One fourth of the code weight, as an integer. -/
def sourceCodeQuarterWeight (d : Fin 4096) : ℤ :=
  (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)

/-- The integral carry identity, before taking the lattice quotient. -/
theorem leechTwiceCodeWordLift_add (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    leechTwiceCodeWordLift d + leechTwiceCodeWordLift e - leechTwiceCodeWordLift f +
      leechCocodeLift (sourceCodeIntersection d e) =
        (sourceCodeQuarterWeight d + sourceCodeQuarterWeight e - sourceCodeQuarterWeight f) •
          leechTwiceCodeWordLift 2048 := by
  apply Subtype.ext
  funext i
  have hΩ : (golayEncodedMask 2048).testBit i.val = true := by
    fin_cases i <;> decide
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, leechTwiceCodeWordLift,
    leechTwiceCodeWordVector, leechCocodeLift]
  change 2 * sourceCodeInteger d i + 2 * sourceCodeInteger e i -
    2 * sourceCodeInteger f i + ((∑ j, sourceCodeIntersection d e j) -
      4 * sourceCodeIntersection d e i) =
      (sourceCodeQuarterWeight d + sourceCodeQuarterWeight e - sourceCodeQuarterWeight f) *
        (2 * if (golayEncodedMask 2048).testBit i.val then 1 else 0)
  rw [hΩ]
  simp only [ite_true, mul_one]
  rw [sourceCodeIntersection_sum d e f hf]
  have h := sourceCodeInteger_add d e f hf i
  simp only [sourceCodeQuarterWeight]
  linarith

/-- Binary hyperbolic coordinates of an actual integral lattice vector. -/
noncomputable def sourceLatticeCoordinates : leechIntegral →+ (Fin 24 → ZMod 2) :=
  leechHyperbolicCoordinates.toAddMonoidHom.comp leechReduction

theorem sourceBinary_zsmul_apply (n : ℤ) (v : Fin 24 → ZMod 2) (i : Fin 24) :
    (n • v) i = (n : ZMod 2) * v i := by
  rw [Pi.smul_apply]
  change n • v i = (n : ZMod 2) • v i
  exact (Int.cast_smul_eq_zsmul (R := ZMod 2) n (v i)).symm

/-- Normalization contributes the fourth-weight multiple of the all-one word.
The sign of a representative disappears in the actual quotient Λ/2Λ. -/
theorem leechSourceCodeWordLift_normalized_coordinates (d : Fin 4096) :
    sourceLatticeCoordinates (leechSourceCodeWordLift d) =
      sourceLatticeCoordinates (leechTwiceCodeWordLift d) +
        sourceCodeQuarterWeight d • sourceLatticeCoordinates (leechTwiceCodeWordLift 2048) := by
  have hw := golayEncodedMask_weights d
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | hw | hw | hw | hw
  all_goals
    ext i
    have hn : ∀ a : ZMod 2, -a = a := by decide +kernel
    simp [leechSourceCodeWordLift, hw, sourceCodeQuarterWeight,
      show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide,
      sub_eq_add_neg, hn, add_comm]

/-- Normalized code words add with the intersection cocode prescribed by the
source group law. This uses the actual Leech quotient, with no coordinate
compatibility hypothesis. -/
theorem leechSourceCodeWordLift_add (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    sourceLatticeCoordinates (leechSourceCodeWordLift d) +
      sourceLatticeCoordinates (leechSourceCodeWordLift e) =
    sourceLatticeCoordinates (leechSourceCodeWordLift f) +
      binaryCocodeEmbedding (golaySyndrome (integerParity (sourceCodeIntersection d e))) := by
  have h := congrArg sourceLatticeCoordinates (leechTwiceCodeWordLift_add d e f hf)
  simp only [map_add, map_sub, map_zsmul] at h
  have hc : sourceLatticeCoordinates (leechCocodeLift (sourceCodeIntersection d e)) =
      binaryCocodeEmbedding (golaySyndrome (integerParity (sourceCodeIntersection d e))) :=
    leechCocodeLift_coordinates _
  rw [hc] at h
  simp_rw [leechSourceCodeWordLift_normalized_coordinates]
  ext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.sub_apply, sourceBinary_zsmul_apply, Int.cast_add,
    Int.cast_sub] at hi ⊢
  have hn : ∀ a : ZMod 2, -a = a := by decide +kernel
  simp only [sub_eq_add_neg, hn] at hi
  linear_combination (norm := skip) hi
  ring_nf
  simp [show (2 : ZMod 2) = 0 by decide]


/-- Two quadratic coordinate maps with the same polarization agree when they
agree on a binary basis. -/
theorem sourceQuadraticCoordinates_eq
    (F G : (Fin 12 → ZMod 2) → (Fin 24 → ZMod 2))
    (B : (Fin 12 → ZMod 2) → (Fin 12 → ZMod 2) → (Fin 24 → ZMod 2))
    (hzero : F 0 = G 0)
    (hF : ∀ a b, F (a + b) = F a + F b + B a b)
    (hG : ∀ a b, G (a + b) = G a + G b + B a b)
    (hbasis : ∀ j : Fin 12, F (Pi.single j 1) = G (Pi.single j 1)) : F = G := by
  let D : (Fin 12 → ZMod 2) →+ (Fin 24 → ZMod 2) :=
    { toFun := fun a => F a - G a
      map_zero' := sub_eq_zero.mpr hzero
      map_add' := by
        intro a b
        change F (a + b) - G (a + b) = (F a - G a) + (F b - G b)
        rw [hF, hG]
        abel }
  let L : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
    { D with map_smul' := ZMod.map_smul D }
  have hL : L = 0 := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.zero_apply]
    change F (Pi.single j 1) - G (Pi.single j 1) = 0
    exact sub_eq_zero.mpr (hbasis j)
  funext a
  have h := LinearMap.congr_fun hL a
  change F a - G a = 0 at h
  exact sub_eq_zero.mp h

/-- Convert a binary coefficient vector to its unique finite code label. -/
noncomputable def sourceCodeLabelEquiv : Fin 4096 ≃ (Fin 12 → ZMod 2) :=
  Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective

/-- Actual normalized source lifts, indexed by their binary coefficient vectors. -/
noncomputable def sourceCodeCoordinates (a : Fin 12 → ZMod 2) : Fin 24 → ZMod 2 :=
  sourceLatticeCoordinates (leechSourceCodeWordLift (sourceCodeLabelEquiv.symm a))

/-- Actual code-coordinate addition in binary coefficient notation. -/
theorem sourceCodeCoordinates_add (a b : Fin 12 → ZMod 2) :
    sourceCodeCoordinates (a + b) = sourceCodeCoordinates a + sourceCodeCoordinates b +
      binaryCocodeEmbedding (golaySyndrome (fun i => golayEncoder a i * golayEncoder b i)) := by
  let d := sourceCodeLabelEquiv.symm a
  let e := sourceCodeLabelEquiv.symm b
  let f := sourceCodeLabelEquiv.symm (a + b)
  have hd : golayLabelCoefficients d = a := sourceCodeLabelEquiv.apply_symm_apply a
  have he : golayLabelCoefficients e = b := sourceCodeLabelEquiv.apply_symm_apply b
  have hf : golayLabelCoefficients f = a + b := sourceCodeLabelEquiv.apply_symm_apply (a + b)
  have hi : integerParity (sourceCodeIntersection d e) =
      fun i => golayEncoder a i * golayEncoder b i := by
    ext i
    change ((sourceCodeInteger d i * sourceCodeInteger e i : ℤ) : ZMod 2) = _
    rw [Int.cast_mul]
    have hbit (x : Fin 4096) : (sourceCodeInteger x i : ZMod 2) =
        golayEncoder (golayLabelCoefficients x) i := by
      apply ZMod.val_injective
      cases hb : (golayEncodedMask x.val).testBit i.val <;>
        simpa [sourceCodeInteger, hb, show (1 : ZMod 2).val = 1 by decide]
          using (golayLabelEncoder_match x i).symm
    rw [hbit, hbit, hd, he]
  have h := leechSourceCodeWordLift_add d e f (by rw [hd, he, hf])
  rw [hi] at h
  change sourceCodeCoordinates a + sourceCodeCoordinates b =
    sourceCodeCoordinates (a + b) + _ at h
  have hn : ∀ x : Fin 24 → ZMod 2, x + x = 0 := by
    intro x
    ext i
    change x i + x i = 0
    calc x i + x i = (2 : ZMod 2) * x i := by ring
         _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  have h' := congrArg (fun x => x +
    binaryCocodeEmbedding (golaySyndrome (fun i => golayEncoder a i * golayEncoder b i))) h
  simpa only [add_assoc, hn, add_zero] using h'.symm

/-- The finite source labels agree with the ordinary binary basis. -/
theorem sourceCodeGeneratorLabel_coefficients (j : Fin 12) :
    golayLabelCoefficients (sourceCodeGeneratorLabel j) = Pi.single j 1 := by
  fin_cases j <;> decide +kernel

/-- The actual normalized zero word has zero lattice class. -/
theorem sourceCodeCoordinates_zero : sourceCodeCoordinates 0 = 0 := by
  have hlabel : sourceCodeLabelEquiv.symm 0 = (0 : Fin 4096) := by
    apply sourceCodeLabelEquiv.injective
    rw [sourceCodeLabelEquiv.apply_symm_apply]
    ext j
    simp [sourceCodeLabelEquiv, golayLabelCoefficients]
  have hzero : leechSourceCodeWordLift 0 = 0 := by
    apply Subtype.ext
    rw [leechSourceCodeWordLift_vector]
    change leechSourceCodeWordVector 0 = (0 : Fin 24 → ℤ)
    decide +kernel
  rw [sourceCodeCoordinates, hlabel, hzero, map_zero]

/-- The source-coordinate generator cases in coefficient notation. -/
theorem sourceCodeCoordinates_generator (j : Fin 12) :
    sourceCodeCoordinates (Pi.single j 1) =
      Pi.single (Fin.castAdd 12 j) 1 + binaryCocodeEmbedding (sourceCodeTheta j) := by
  have hlabel : sourceCodeLabelEquiv.symm (Pi.single j 1) = sourceCodeGeneratorLabel j := by
    apply sourceCodeLabelEquiv.injective
    rw [sourceCodeLabelEquiv.apply_symm_apply]
    exact (sourceCodeGeneratorLabel_coefficients j).symm
  rw [sourceCodeCoordinates, hlabel]
  exact leechSourceCodeWordLift_generator_hyperbolic j

/-- Code and nonlinear Parker theta coordinates, combined in the fixed frame. -/
def sourceExpectedCodeCoordinates (a : Fin 12 → ZMod 2) : Fin 24 → ZMod 2 :=
  Fin.append a (sourceCodeThetaPolynomial a)

/-- All normalized source code words have their published spin coordinates.
The extension from twelve generators uses the actual lattice carry identity
and the Parker theta polarization, rather than a list of short-vector checks. -/
theorem sourceCodeCoordinates_eq (a : Fin 12 → ZMod 2) :
    sourceCodeCoordinates a = sourceExpectedCodeCoordinates a := by
  have h := sourceQuadraticCoordinates_eq sourceCodeCoordinates sourceExpectedCodeCoordinates
    (fun a b => binaryCocodeEmbedding
      (golaySyndrome (fun i => golayEncoder a i * golayEncoder b i))) ?_ sourceCodeCoordinates_add
    ?_ ?_
  · exact congrFun h a
  · rw [sourceCodeCoordinates_zero]
    ext i
    refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i
    · simp only [sourceExpectedCodeCoordinates, sourceCodeThetaPolynomial_zero,
        Fin.append_left, Pi.zero_apply]
    · simp only [sourceExpectedCodeCoordinates, sourceCodeThetaPolynomial_zero,
        Fin.append_right, Pi.zero_apply]
  · intro a b
    ext i
    refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i
    · simp only [sourceExpectedCodeCoordinates, Fin.append_left, Pi.add_apply,
        binaryCocodeEmbedding_left, add_zero]
    · simpa only [sourceExpectedCodeCoordinates, Fin.append_right, Pi.add_apply,
        binaryCocodeEmbedding_right] using congrFun (sourceCodeThetaPolynomial_add a b) j
  · intro j
    rw [sourceCodeCoordinates_generator]
    ext i
    refine Fin.addCases (m := 12) (n := 12) (fun k => ?_) (fun k => ?_) i
    · simp only [sourceExpectedCodeCoordinates, Fin.append_left, Pi.add_apply,
        binaryCocodeEmbedding_left, add_zero, Pi.single_apply]
      have heq : Fin.castAdd 12 k = Fin.castAdd 12 j ↔ k = j := Fin.castAdd_inj
      simp only [heq]
    · simp only [sourceExpectedCodeCoordinates, Fin.append_right, Pi.add_apply,
        binaryCocodeEmbedding_right, sourceCodeThetaPolynomial_single]
      have hne : Fin.natAdd 12 k ≠ Fin.castAdd 12 j := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      simp only [Pi.single_apply, hne, ite_false, zero_add]

/-- The complete normalized code-word lift dictionary in the actual Leech
quotient and the actual Parker theta coordinates. -/
theorem leechSourceCodeWordLift_hyperbolic (d : Fin 4096) :
    leechHyperbolicCoordinates (leechReduction (leechSourceCodeWordLift d)) =
      Fin.append (golayLabelCoefficients d)
        (fun k : Fin 12 => if (parkerThetaMask d.val).testBit k.val then 1 else 0) := by
  have h := sourceCodeCoordinates_eq (golayLabelCoefficients d)
  have hlabel : sourceCodeLabelEquiv.symm (golayLabelCoefficients d) = d :=
    sourceCodeLabelEquiv.symm_apply_apply d
  rw [sourceCodeCoordinates, hlabel, sourceExpectedCodeCoordinates] at h
  have htheta : sourceCodeThetaPolynomial (golayLabelCoefficients d) =
      fun k : Fin 12 => if (parkerThetaMask d.val).testBit k.val then 1 else 0 := by
    ext k
    exact (sourceCodeThetaPolynomial_mask d k).symm
  rw [htheta] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
