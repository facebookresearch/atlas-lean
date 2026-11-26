# Ben-Sasson–Wigderson for general resolution

There is an absolute constant $c$ such that if a CNF formula $F$ in $n$ variables has a [resolution refutation](is-resolution-refutation.md) with $S$ lines, then it has a refutation of [width](derivation-width.md) at most $w(F) + c\sqrt{n \ln S}$. Equivalently,

$$S(F) = \exp\left(\Omega\left(\frac{(w(F \vdash 0) - w(F))^2}{n}\right)\right).$$

The proof removes "fat" clauses, of width more than $d = \lceil\sqrt{2n \ln S}\rceil$: by pigeonhole some literal lies in at least a $d/2n$ fraction of them, and setting it to true removes that fraction, so after about $\sqrt{2n \ln S}$ restrictions none are left; the restrictions are recombined as in the [tree-like case](tree-refutation-narrow.md). Since $n$ appears in the bound, it gives strong size lower bounds only when the width lower bound is much larger than $\sqrt{n}$, as for Tseitin formulas on expanders and random $3$-CNFs.

## Sources

- E. Ben-Sasson and A. Wigderson, Short proofs are narrow — resolution made simple, J. ACM 48 (2001), 149-169, Theorem 3.5 and Corollary 3.6.
