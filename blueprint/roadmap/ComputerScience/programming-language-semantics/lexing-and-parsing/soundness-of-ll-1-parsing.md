# Soundness of LL(1) parsing

Let $\mathrm{parse}$ be the table-driven LL(1) parser that, given a table, a grammar symbol $s$ and a token sequence, either returns a semantic value and the unconsumed suffix or reports an error, and that stops with an error when it would re-enter a nonterminal that is still active at the same input position. At a nonterminal $X$ with lookahead $l$ it applies the production $X \to \gamma\ \{f\}$ stored at $(X, l)$, parses $\gamma$ and returns $f$ applied to the values obtained. If the table is [correct](ll-1-lookahead-and-correct-parse-tables.md) for $G$ and $\mathrm{parse}(s, w \cdot r)$ returns the value $v$ and the suffix $r$, then $s \xrightarrow{v} w \mid r$ in the LL(1) derivation relation of $G$.

**Proof idea.** A more general statement for the mutually recursive functions that parse a symbol and a list of symbols, proved by nested induction on the lexicographic termination measure (remaining input length, then the number of unvisited nonterminals, then the size of the symbol or list of symbols being parsed); the successful path of the parser follows the derivation rules.

## Depends on

- [LL(1) lookahead and correct parse tables](ll-1-lookahead-and-correct-parse-tables.md)

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *10th International Conference on Interactive Theorem Proving (ITP 2019)*, LIPIcs 141, 2019, 24:1–24:18, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf>, Section 4.1 (the parser and its termination measure, a triple of natural numbers ordered lexicographically) and Section 4.2, Theorem parse_sound and Lemma parseSymbol_sound.
