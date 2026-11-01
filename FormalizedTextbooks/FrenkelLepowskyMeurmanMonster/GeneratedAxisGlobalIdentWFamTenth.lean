/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Factory glue for the Tenth source (goctad)

The identification factory needs, per family, a source vector with a kernel-cheap literal short
block, a packed tensor block with a numeric bound, the representation lemma for every large width,
and the matrix block as an integer block (pattern of `GeneratedAxisGlobalIdentWFamFourth`).  For
the Tenth family (representative `11`) these are provided by the gated module
`GeneratedAxisGlobalIdentSrcTenthCF` and collected here:
* the source vector `tenthSrcVecL w`, with matrix block `srcTenthMat`, short block
  `srcTenthCShort`, short scale `1 / 128` and tensor block `tensorRat w (tenthSrcXL w) 32`;
* the structured literal short block `srcTenthCShort` (pair terms, octad blocks decoded in
  chunks of `120` octads, odd terms column by column), kernel-certified against the triality
  image;
* the compact tensor `tenthSrcXL w = twWidenT 4 w srcTenthCXLit` (numerators over `32`) with
  the numeric bound `15` for every `w ≥ 4`;
* the integer matrix block `srcTenthMatZ` with `srcTenthMat_act_entryZ`.

`wfamTenth_interface` states these facts in one place.  `wfamTenth_flat` certifies the flat
short list used by the factory: 46082 terms (312 pair, 22346 octad, 23424 odd terms),
numerators of absolute value at most `32` (so the factory's `8`-bit packed target lists apply),
and a fingerprint of the exact term order (the order of the factory's flat source list). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The factory interface of the Tenth source: the representation of family representative
`11` at every width `w ≥ 4`, the literal blocks and scale, the compact tensor block with its
numeric bound, the range conditions of the short block and the integer matrix glue. -/
theorem wfamTenth_interface {w : ℕ} (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 11) =
        (tenthSrcVecL w).real ∧
      (tenthSrcVecL w).mat = srcTenthMat ∧
      (tenthSrcVecL w).sh = srcTenthCShort ∧
      (tenthSrcVecL w).sden = 1 / 128 ∧
      (tenthSrcVecL w).ten = tensorRat w (tenthSrcXL w) 32 ∧
      TBnd w 15 (tenthSrcXL w) ∧
      srcTenthCShort.ok = true ∧
      ∀ (ls : List IdentLetter) (i j : Fin 24),
        (srcTenthMat.act identSpatialAlphabet ls).entry i j =
          (srcTenthMatZ.act ls).entry i j :=
  ⟨tenthSrcL_rep hw, rfl, rfl, rfl, rfl, tenthSrcXL_bnd hw, tenthSrcVecL_ok w,
    srcTenthMat_act_entryZ⟩

set_option maxRecDepth 100000 in
/-- The flat short list of the Tenth source: its length, the numerator bound `32`, and the
fingerprint `h ↦ (1000003 h + 512 label + numerator + 256) mod (2 ^ 61 - 1)` of the term
order. -/
theorem wfamTenth_flat :
    srcTenthCShort.flat.length = 46082 ∧
      srcTenthCShort.flat.all (fun p => decide (p.2.natAbs ≤ 32)) = true ∧
      srcTenthCShort.flat.foldl
          (fun h p => (h * 1000003 + p.1 * 512 + (p.2 + 256).toNat) % 2305843009213693951) 0 =
        1674583187604553160 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
