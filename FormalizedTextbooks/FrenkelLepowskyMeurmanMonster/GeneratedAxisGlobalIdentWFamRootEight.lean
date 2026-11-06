/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory glue for the Root8 source (goctad)

The identification factory needs, per family, a source vector with a kernel-cheap literal short
block, a packed tensor block with a numeric bound, the representation lemma for every large width,
and the matrix block as an integer block (pattern of `GeneratedAxisGlobalIdentWFamFourth`).  For
the Root8 family (representative `9`) these are provided by the gated module
`GeneratedAxisGlobalIdentSrcRootEightCF` and collected here:
* the source vector `rootEightSrcVecL w`, with matrix block `srcRootEightMat`, short block
  `srcRootEightCShort`, short scale `1 / 128` and tensor block `tensorRat w (rootEightSrcXL w) 32`;
* the structured literal short block `srcRootEightCShort` (pair terms, octad blocks decoded in
  chunks of `120` octads, odd terms column by column), kernel-certified against the triality
  image;
* the compact tensor `rootEightSrcXL w = twWidenT 4 w srcRootEightCXLit` (numerators over `32`) with
  the numeric bound `15` for every `w ≥ 4`;
* the integer matrix block `srcRootEightMatZ` with `srcRootEightMat_act_entryZ`.

`wfamRootEight_interface` states these facts in one place.  `wfamRootEight_flat` certifies the flat
short list used by the factory: 33576 terms (328 pair, 16864 octad, 16384 odd terms),
numerators of absolute value at most `32` (so the factory's `8`-bit packed target lists apply),
and a fingerprint of the exact term order (the order of the factory's flat source list). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The factory interface of the Root8 source: the representation of family representative
`9` at every width `w ≥ 4`, the literal blocks and scale, the compact tensor block with its
numeric bound, the range conditions of the short block and the integer matrix glue. -/
theorem wfamRootEight_interface {w : ℕ} (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 9) =
        (rootEightSrcVecL w).real ∧
      (rootEightSrcVecL w).mat = srcRootEightMat ∧
      (rootEightSrcVecL w).sh = srcRootEightCShort ∧
      (rootEightSrcVecL w).sden = 1 / 128 ∧
      (rootEightSrcVecL w).ten = tensorRat w (rootEightSrcXL w) 32 ∧
      TBnd w 15 (rootEightSrcXL w) ∧
      srcRootEightCShort.ok = true ∧
      ∀ (ls : List IdentLetter) (i j : Fin 24),
        (srcRootEightMat.act identSpatialAlphabet ls).entry i j =
          (srcRootEightMatZ.act ls).entry i j :=
  ⟨rootEightSrcL_rep hw, rfl, rfl, rfl, rfl, rootEightSrcXL_bnd hw, rootEightSrcVecL_ok w,
    srcRootEightMat_act_entryZ⟩

set_option maxRecDepth 100000 in
/-- The flat short list of the Root8 source: its length, the numerator bound `32`, and the
fingerprint `h ↦ (1000003 h + 512 label + numerator + 256) mod (2 ^ 61 - 1)` of the term
order. -/
theorem wfamRootEight_flat :
    srcRootEightCShort.flat.length = 33576 ∧
      srcRootEightCShort.flat.all (fun p => decide (p.2.natAbs ≤ 32)) = true ∧
      srcRootEightCShort.flat.foldl
          (fun h p => (h * 1000003 + p.1 * 512 + (p.2 + 256).toNat) % 2305843009213693951) 0 =
        252626956607863692 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
