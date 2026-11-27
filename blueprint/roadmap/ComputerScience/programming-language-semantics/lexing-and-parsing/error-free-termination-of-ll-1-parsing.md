# Error-free termination of LL(1) parsing

For the table-driven parser of [soundness of LL(1) parsing](soundness-of-ll-1-parsing.md), if its table is [correct](ll-1-lookahead-and-correct-parse-tables.md) for some grammar, then $\mathrm{parse}(s, ts)$ never returns the error that signals a revisited nonterminal: it either returns a value or rejects the input.

**Proof idea.** The parser reports that error only when its set of visited nonterminals already contains a nonterminal reachable by a nullable path from the current symbol, or when the grammar is left recursive on the current lookahead symbol, in the sense of [the left-recursion lemma](ll-1-grammars-have-no-left-recursion.md). The top-level call starts with an empty visited set, and [LL(1) grammars have no left recursion](ll-1-grammars-have-no-left-recursion.md).

## Depends on

- [Soundness of LL(1) parsing](soundness-of-ll-1-parsing.md)
- [LL(1) lookahead and correct parse tables](ll-1-lookahead-and-correct-parse-tables.md)

## Proof depends on

- [LL(1) grammars have no left recursion](ll-1-grammars-have-no-left-recursion.md)

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *10th International Conference on Interactive Theorem Proving (ITP 2019)*, LIPIcs 141, 2019, 24:1–24:18, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf>, Section 4.3, Theorem parse_terminates_without_error and the error conditions nullable_path and left_recursive.
