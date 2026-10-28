/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcNinthCF

/-! # Factory glue for the Ninth source (goctad)

The identification factory needs, per family, a source vector with a kernel-cheap literal short
block, a packed tensor block with a numeric bound, the representation lemma for every large width,
and the matrix block as an integer block (pattern of `GeneratedAxisGlobalIdentWFamFourth`).  For
the Ninth family (representative `8`) these are provided by the gated module
`GeneratedAxisGlobalIdentSrcNinthCF` and collected here:
* the source vector `ninthSrcVecL w`, with matrix block `srcNinthMat`, short block
  `srcNinthCShort`, short scale `1 / 128` and tensor block `tensorRat w (ninthSrcXL w) 32`;
* the structured literal short block `srcNinthCShort` (pair terms, octad blocks decoded in
  chunks of `120` octads, odd terms column by column), kernel-certified against the triality
  image;
* the compact tensor `ninthSrcXL w = twWidenT 4 w srcNinthCXLit` (numerators over `32`) with
  the numeric bound `15` for every `w ≥ 4`;
* the integer matrix block `srcNinthMatZ` with `srcNinthMat_act_entryZ`.

`wfamNinth_interface` states these facts in one place.  `wfamNinth_flat` certifies the flat
short list used by the factory: 61584 terms (264 pair, 30472 octad, 30848 odd terms),
numerators of absolute value at most `32` (so the factory's `8`-bit packed target lists apply),
and a fingerprint of the exact term order (the order of the factory's flat source list). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The factory interface of the Ninth source: the representation of family representative
`8` at every width `w ≥ 4`, the literal blocks and scale, the compact tensor block with its
numeric bound, the range conditions of the short block and the integer matrix glue. -/
theorem wfamNinth_interface {w : ℕ} (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 8) =
        (ninthSrcVecL w).real ∧
      (ninthSrcVecL w).mat = srcNinthMat ∧
      (ninthSrcVecL w).sh = srcNinthCShort ∧
      (ninthSrcVecL w).sden = 1 / 128 ∧
      (ninthSrcVecL w).ten = tensorRat w (ninthSrcXL w) 32 ∧
      TBnd w 15 (ninthSrcXL w) ∧
      srcNinthCShort.ok = true ∧
      ∀ (ls : List IdentLetter) (i j : Fin 24),
        (srcNinthMat.act identSpatialAlphabet ls).entry i j =
          (srcNinthMatZ.act ls).entry i j :=
  ⟨ninthSrcL_rep hw, rfl, rfl, rfl, rfl, ninthSrcXL_bnd hw, ninthSrcVecL_ok w,
    srcNinthMat_act_entryZ⟩

set_option maxRecDepth 100000 in
/-- The flat short list of the Ninth source: its length, the numerator bound `32`, and the
fingerprint `h ↦ (1000003 h + 512 label + numerator + 256) mod (2 ^ 61 - 1)` of the term
order. -/
theorem wfamNinth_flat :
    srcNinthCShort.flat.length = 61584 ∧
      srcNinthCShort.flat.all (fun p => decide (p.2.natAbs ≤ 32)) = true ∧
      srcNinthCShort.flat.foldl
          (fun h p => (h * 1000003 + p.1 * 512 + (p.2 + 256).toNat) % 2305843009213693951) 0 =
        2076354025450347954 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
