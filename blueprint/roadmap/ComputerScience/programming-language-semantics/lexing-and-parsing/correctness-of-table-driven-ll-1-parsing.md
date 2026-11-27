# Correctness of table-driven LL(1) parsing

Let $G$ be a grammar with a [correct LL(1) parse table](ll-1-lookahead-and-correct-parse-tables.md), and let $\mathrm{parse}$ be the table-driven parser of [soundness of LL(1) parsing](soundness-of-ll-1-parsing.md). Then $\mathrm{parse}$ is sound and complete *for prefixes* with respect to the LL(1) derivation relation of $G$: for every grammar symbol $s$, token sequences $w, r$ and semantic value $v$,

$$\mathrm{parse}(s, w \cdot r) \text{ returns } (v, r) \iff s \xrightarrow{v} w \mid r,$$

and on every input it terminates, either with a value or by rejecting, never with the error that signals left recursion. This is not whole-input acceptance in the sense of [parsers and recognizers](parsers-and-recognizers.md): with the single production $S \to a$, $\mathrm{parse}(S, a\,a)$ returns the value of the first token and the remainder $a$, although $a\,a$ is not in the language. A whole input $w$ is accepted, with value $v$, exactly when $\mathrm{parse}(S, w)$ returns $(v, \varepsilon)$ for the start symbol $S$, which by the biconditional means $S \xrightarrow{v} w \mid \varepsilon$.

**Proof.** The forward direction is [soundness](soundness-of-ll-1-parsing.md), the backward direction is [completeness](completeness-of-ll-1-parsing.md), and termination without error is [error-free termination](error-free-termination-of-ll-1-parsing.md).

## Depends on

- [LL(1) lookahead and correct parse tables](ll-1-lookahead-and-correct-parse-tables.md)
- [Parsers and recognizers](parsers-and-recognizers.md)
- [Soundness of LL(1) parsing](soundness-of-ll-1-parsing.md)

## Proof depends on

- [Completeness of LL(1) parsing](completeness-of-ll-1-parsing.md)
- [Error-free termination of LL(1) parsing](error-free-termination-of-ll-1-parsing.md)

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *10th International Conference on Interactive Theorem Proving (ITP 2019)*, LIPIcs 141, 2019, 24:1–24:18, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf>, Section 4: the parser (4.1) and Theorems parse_sound (4.2), parse_terminates_without_error (4.3) and parse_complete (4.4), which concern prefixes with a remainder.
