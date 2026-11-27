# Completeness of LL(1) parsing

For the table-driven parser of [soundness of LL(1) parsing](soundness-of-ll-1-parsing.md) with a [correct](ll-1-lookahead-and-correct-parse-tables.md) table for $G$: if $s \xrightarrow{v} w \mid r$ in the LL(1) derivation relation of $G$, then $\mathrm{parse}(s, w \cdot r)$ returns $v$ and $r$.

**Proof idea.** By induction on the derivation, the parser either returns an error or returns $v$ and $r$; [error-free termination](error-free-termination-of-ll-1-parsing.md) rules out the error.

## Depends on

- [Soundness of LL(1) parsing](soundness-of-ll-1-parsing.md)
- [LL(1) lookahead and correct parse tables](ll-1-lookahead-and-correct-parse-tables.md)

## Proof depends on

- [Error-free termination of LL(1) parsing](error-free-termination-of-ll-1-parsing.md)

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *10th International Conference on Interactive Theorem Proving (ITP 2019)*, LIPIcs 141, 2019, 24:1–24:18, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf>, Section 4.4, Theorem parse_complete and Theorem parseSymbol_error_or_complete.
