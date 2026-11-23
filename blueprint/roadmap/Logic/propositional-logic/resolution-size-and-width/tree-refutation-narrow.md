# Ben-Sasson–Wigderson for tree-like resolution

If a CNF formula $F$ has a [tree-like refutation](resolution-tree.md) with $S$ lines, then it has a [resolution refutation](is-resolution-refutation.md) of [width](derivation-width.md) at most $w(F) + \log_2 S$, where $w(F)$ is the [largest width of a clause of $F$](max-clause-width.md). It is stated as $2^{\text{width}} \le 2^{w(F)} \cdot S$. Equivalently, the minimal tree-like refutation size satisfies

$$S_T(F) \ge 2^{\,w(F \vdash 0) - w(F)},$$

where $w(F \vdash 0)$ is the minimal width of a refutation.

The proof is by induction on $\log_2 S$ and on the number of variables. The last step of the tree resolves the unit clauses $x$ and $\neg x$, and one of the two subtrees, say the one deriving $x^{a}$ (where $x^1 = x$ and $x^0 = \neg x$), has at most half the lines. Restricted by $x = 1 - a$ it refutes $F|_{x = 1-a}$, so by induction $F|_{x = 1-a}$ has a refutation of width at most $w(F) + \log_2 S - 1$, and Lemma 3.1 turns it into a derivation of $x^{a}$ from $F$ of width one more. Lemma 3.2 combines this derivation with a narrow refutation of $F|_{x = a}$, obtained by induction on the number of variables.

## Sources

- E. Ben-Sasson and A. Wigderson, Short proofs are narrow — resolution made simple, J. ACM 48 (2001), 149-169, Lemmas 3.1-3.2, Theorem 3.3 and Corollary 3.4.
