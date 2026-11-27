# Tree-like resolution derivation

A tree-like derivation of the clause `C` from the
clauses of `φ`: a leaf is a clause of `φ`, an inner node applies the resolution rule (from
`E ∨ x` and `F ∨ ¬x` derive `E ∨ F`) or the weakening rule (from `E` derive any clause
containing all literals of `E`). Clauses of `φ` may be used at several leaves (Ben-Sasson and
Wigderson, J. ACM 48 (2001), Section 2.1).

The minimum, over tree-like refutations of $F$, of the [size](proof-size.md) is the tree-like refutation size $S_T(F)$ of Ben-Sasson and Wigderson; general derivations are [sequences of lines](is-resolution-derivation.md).
