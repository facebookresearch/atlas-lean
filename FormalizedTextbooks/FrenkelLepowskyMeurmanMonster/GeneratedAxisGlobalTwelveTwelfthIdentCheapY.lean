/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentCheapS1

/-! # The incoming Twelfth vector with a cheap packed tensor

The source word of the Twelfth axis has three nonempty stages. The packed tensor of the incoming
vector `y = rhoLocal generatedTwelfthLocal v₅` is computed part by part from compact literals: the
kernel checks four steps (monomial letters, then Xi and the code sign, for each of the first two
stages; small field widths, each a separate evaluation), and the third stage (one code sign) is
applied to the widened `twelfthS1Lit` (`twelfthYXC`). `twelfthYC` represents `y` with this tensor
(`twelfthYC_actual`); it differs from `twelfthYLit` only in the tensor block. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word in its three nonempty stages. -/
theorem twelfthYWord_stages :
    twelfthYWord = twelfthYStage 2 ++ (twelfthYStage 1 ++ twelfthYStage 0) := by
  rfl

/-- The cheap packed tensor of the incoming vector (numerators over `64`). -/
def twelfthYXC : List SVec :=
  tensorWordAll 24 (twelfthYStage 2) (twWidenT 3 24 twelfthS1Lit)

/-- Bounds of the cheap incoming tensor. -/
theorem twelfthYXC_bnd : TBnd 24 56 twelfthYXC := by
  obtain ⟨-, -, -, -, -, -, -, -, -, g2⟩ := twelfthYStage_dens
  have h := (tensorWordAll_actual (twelfthYStage 2) (twWidenT_bnd 3 24 (by norm_num) twelfthS1Lit)
    (by rw [g2]; norm_num) 32).1
  rw [g2] at h
  exact h

/-- The three stages carry the Fifth tensor to the cheap incoming tensor. -/
theorem twelfthY_tensor_chain :
    localTensorRepresentation (identWordFiber twelfthYWord)
        (generatedAxisGlobalRationalTensorReal (tensorRat 24 (fifthSrcXW 24) 1)) =
      generatedAxisGlobalRationalTensorReal (tensorRat 24 twelfthYXC 64) := by
  obtain ⟨d0m, g0m, d0x, g0x, d1m, g1m, d1x, g1x, d2, g2⟩ := twelfthYStage_dens
  rw [twelfthYWord_stages, twelfthYStage_split 0, twelfthYStage_split 1]
  simp only [identWordFiber_append, map_mul, LinearEquiv.mul_apply]
  have e5 : generatedAxisGlobalRationalTensorReal (tensorRat 24 (fifthSrcXW 24) 1) =
      generatedAxisGlobalRationalTensorReal (tensorRat 8 (fifthSrcXW 8) 1) := by
    have h1 := (fifthSrcW_rep (w := 24) (by norm_num)).symm.trans
      (fifthSrcW_rep (w := 8) (by norm_num))
    have h2 := congrArg (fun z => z.2.2) h1
    simp only [IdentVec.real_tensor] at h2
    exact h2
  rw [e5]
  have a0m := tensorWordAll_actual ((twelfthYStage 0).drop 2)
    (fifthSrcXW_bnd (w := 8) (by norm_num))
    (by rw [g0m]; norm_num) 1
  rw [g0m] at a0m
  rw [a0m.2, d0m, twColCheck_rat 8 2 1 _ _ _ (by norm_num) a0m.1 (by norm_num) twelfthS0m_check _ 1
    (by norm_num) (by norm_num), ← twWidenT_rat 2 16 (by norm_num) twelfthS0mLit 1]
  have a0x := tensorWordAll_actual ((twelfthYStage 0).take 2)
    (twWidenT_bnd 2 16 (by norm_num) twelfthS0mLit) (by rw [g0x]; norm_num) 1
  rw [g0x] at a0x
  rw [a0x.2, d0x, twColCheck_rat 16 2 4 _ _ _ (by norm_num) a0x.1 (by norm_num) twelfthS0_check _ 8
    (by norm_num) (by norm_num), ← twWidenT_rat 2 4 (by norm_num) twelfthS0Lit 8]
  have a1m := tensorWordAll_actual ((twelfthYStage 1).drop 2)
    (twWidenT_bnd 2 4 (by norm_num) twelfthS0Lit) (by rw [g1m]; norm_num) 8
  rw [g1m] at a1m
  rw [a1m.2, d1m, twColCheck_rat 4 2 1 _ _ _ (by norm_num) a1m.1 (by norm_num) twelfthS1m_check _ 8
    (by norm_num) (by norm_num), ← twWidenT_rat 2 16 (by norm_num) twelfthS1mLit 8]
  have a1x := tensorWordAll_actual ((twelfthYStage 1).take 2)
    (twWidenT_bnd 2 16 (by norm_num) twelfthS1mLit) (by rw [g1x]; norm_num) 8
  rw [g1x] at a1x
  rw [a1x.2, d1x, twColCheck_rat 16 3 8 _ _ _ (by norm_num) a1x.1 (by norm_num) twelfthS1_check _ 32
    (by norm_num) (by norm_num), ← twWidenT_rat 3 24 (by norm_num) twelfthS1Lit 32]
  have h2 := (tensorWordAll_actual (twelfthYStage 2) (twWidenT_bnd 3 24 (by norm_num) twelfthS1Lit)
    (by rw [g2]; norm_num) 32).2
  rw [h2, d2]
  norm_num [twelfthYXC]

/-- The incoming Twelfth vector with the literal matrix block and the cheap tensor. -/
def twelfthYC : IdentVec :=
  ⟨twelfthYMatLit, ShortData.ofList twelfthYT, 1 / 16, tensorRat 24 twelfthYXC 64⟩

/-- The cheap incoming representation is exact. -/
theorem twelfthYC_actual :
    griessConwayEncode (rhoLocal generatedTwelfthLocal generatedFifthAxis) = twelfthYC.real := by
  have hT' : localTensorRepresentation
      (identWordFiber ((twelfthWordData twelfthYWord).map Prod.fst))
      (generatedAxisGlobalRationalTensorReal (fifthSrcVecW 24).ten) =
      generatedAxisGlobalRationalTensorReal (tensorRat 24 twelfthYXC 64) := by
    rw [twelfthWordData_fst]
    exact twelfthY_tensor_chain
  have h := IdentVec.word_actual (fifthSrcVecW 24) (twelfthWordData twelfthYWord) twelfthY_letters
    twelfthYD twelfthY_composite.1 twelfthY_composite.2.1 twelfthY_composite.2.2 twelfthYT
    twelfthY_short _ hT' _ (fifthSrcW_rep (by norm_num))
  rw [twelfthWordData_fst] at h
  rw [← twelfthYWord_local]
  change griessConwayEncode (rhoLocal (identWordLocal twelfthYWord)
    (generatedAxisGlobalTwelveRepresentative 4)) = _
  rw [h]
  unfold twelfthYC
  rw [← twelfthYMat_eq]
  rfl

/-- The short block of the cheap incoming representation satisfies the range conditions. -/
theorem twelfthYC_ok : twelfthYC.sh.ok = true := ofList_ok _ twelfthY_labels

/-- The cheap incoming representation agrees with `twelfthYLit` off the tensor block. -/
theorem twelfthYC_parts :
    twelfthYC.mat = twelfthYLit.mat ∧ twelfthYC.sh = twelfthYLit.sh ∧
      twelfthYC.sden = twelfthYLit.sden := ⟨rfl, rfl, rfl⟩

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
