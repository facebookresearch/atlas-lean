---
article_id: af_1682520625e1e0d91ccb9a59
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.isHadamardMatrix
---

# Is Hadamard Matrix

Hadamard matrix with circulant core (Paley and twin-prime cases).

`isHadamardMatrix m H` is the sign-matrix orthogonality predicate
(entries `±1`, `Hᵀ * H = m • 1`); `hasCirculantCore n H` says the trailing
`n × n` block is circulant, `H (i+1) (j+1) = v (i - j)` with `Fin`
modular difference. The formalized theorem is the prime specialization of
cases (1)–(2): such a matrix of order `n + 1` exists when `n` is a prime
congruent to 3 mod 4 (Paley) or `n = p * (p + 2)` with `p` and `p + 2`
both prime (Stanton–Sprott/Whiteman).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.HadamardCirculantCore](../../../../../../sources/v2/MathlibExt.md)
- Richard P. Brent and Adam B. Yedidia, "Computation of Maximal Determinants of Binary Circulant Matrices," Journal of Integer Sequences 21 (2018), Article 18.5.6, Theorem (label thm:circulant_core), lines 684–695, https://cs.uwaterloo.ca/journals/JIS/VOL21/Brent/brent11.tex quoting Kotsireas et al.; attributions at lines 698–704. The prime-power versions of cases (1)–(2), if the source allows them, and cases (3)–(4) of the source theorem (Singer, Hall) are not formalized here.
