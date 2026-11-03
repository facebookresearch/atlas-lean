# On Solvable Evolution Algebras and a Conjecture by García-Martínez and Pérez-Rodríguez

A Lean 4 formalization of **[On Solvable Evolution Algebras and a Conjecture by
García-Martínez and Pérez-Rodríguez](Papers/evolution_algebras.pdf)**. This paper was [announced by Meta](https://research.meta.ai/blog/solving-open-research-problems-together) on October 2nd, 2026 along with
five others.

[Paper (PDF)](Papers/evolution_algebras.pdf)
· [Interactive paper (HTML)](Papers/evolution_algebras_interactive.html)

Please download the HTML file and open it in your browser.



## About the paper

An **evolution algebra** over a field $K$ is a (nonassociative) $K$-algebra with a distinguished basis $B$, called a **natural basis**, such that $xy=0$ for distinct $x,y\in B$. An evolution algebra is **solvable** if its derived series terminates at zero. We disprove the conjecture proposed by García-Martínez and Pérez-Rodríguez in *A Note on Complete Evolution Algebras* (2026), which states that a complex evolution algebra is solvable if and only if it has no nonzero idempotent elements. Additionally, for finite-dimensional evolution algebras over an algebraically closed field, we introduce idempotent subspaces to properly characterize solvability as well as the existence of nonzero idempotent elements.

| Result | Lean |
|---|---|
| Disproof of G-M and P-R's conjecture | `conjecture_false` <br> [A_Example_2_1_NonSolvableIdempotentFree](Formalization/Section_2_Counterexample/A_Example_2_1_NonSolvableIdempotentFree.lean#L666) |
| Preliminary algebraic geometry result | `fixedPoint_of_idempotent` <br> [A_FixedPoint](Formalization/Appendix_FixedPoint/A_FixedPoint.lean#L52) |
| Characterization of solvable evolution algebras | `solvable_iff_no_idempotent_subspace` <br> [A_Lemma_3_1_Theorem_3_2_SolvableIff](Formalization/Section_3_SolvableAlgebras/A_Lemma_3_1_Theorem_3_2_SolvableIff.lean#L158) |
| Characterization of the existence of idempotent elements in evolution algebras | `IdempotentIff.idempotent_iff` <br> [B_Theorem_3_3_IdempotentElementsAndSubspaces](Formalization/Section_3_SolvableAlgebras/B_Theorem_3_3_IdempotentElementsAndSubspaces.lean#L146) |


## Authorship

The paper was written by Andres Barei with *Muse Spark* via [meta.ai](https://meta.ai), and reviewed by Nicolás Jaramillo Torres.

The formalization was produced and reviewed by Andres Barei, using *Muse Code*.


## Versions

Current version pinned at the top level of this repository: Lean `v4.35.0` and Mathlib `v4.35.0` in [lean-toolchain](../../../lean-toolchain), [lakefile.toml](../../../lakefile.toml), and [lake-manifest.json](../../../lake-manifest.json).

**Formalization published October 30, 2026.**

This paper was originally formalized and verified with:

- Lean `v4.35.0`
- Mathlib `v4.35.0`
- MathlibExt `v2`
