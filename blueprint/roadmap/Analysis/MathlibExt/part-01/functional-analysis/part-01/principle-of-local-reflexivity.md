---
article_id: af_d868cb4c63c8e1659d541735
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.LocalReflexivityWanted.principle_of_local_reflexivity
---

# Local Reflexivity

For a Banach space `E` over `𝕜 = ℝ` or `ℂ`, finite-dimensional `M ↪ E**` via `iM`, `N ↪ E*` via
`iN`, and `ε > 0`, there exists `T : M →L[𝕜] E` that is `(1+ε)`-almost isometric, preserves dual
pairings `(iN n)(T m) = (iM m)(iN n)`, and fixes `J(E)`: `iM m = J x → T m = x`. Source: J.
Lindenstrauss and H. Rosenthal, Israel J. Math. 7 (1969) 325-349, principle of local reflexivity;
Johnson-Rosenthal-Zippin 1971 refinements; Albiac and Kalton, Topics in Banach Space Theory; Lean
states `RCLike` Banach finite- dimensional `M, N` version with `(1+ε)`-isometry and pairing
preservation.

Proof: Helly's lemma applied to finitely many linear conditions plus one norm bound, then a finite
δ-net of the unit sphere of `range iM` turns net-point bounds into the `(1+ε)` bounds (the
elementary proof in Albiac–Kalton, *Topics in Banach Space Theory*).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.LocalReflexivity](../../../../../../sources/v2/MathlibExt.md)
