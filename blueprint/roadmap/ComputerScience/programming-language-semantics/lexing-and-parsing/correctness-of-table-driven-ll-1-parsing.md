# Correctness of table-driven LL(1) parsing

For an LL(1) grammar $G$, the table-driven predictive parser is sound, complete and terminating: every parse tree it returns is a valid derivation tree of $G$ whose yield is the consumed input; it returns a parse tree for every word of $L(G)$; and it terminates on every input when $G$ has no left recursion (which LL(1) grammars cannot have).

## Proof depends on

- [NULLABLE, FIRST, FOLLOW and LL(1) tables](nullable-first-follow-and-ll-1-tables.md)
- [Yields coincide with derivations of terminal words](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/context-free-grammars/yields-iff-derives.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Parser versus recognizer specifications (proof prerequisite; not yet stated)

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *ITP 2019*, LIPIcs 141, 2019
