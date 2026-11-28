# Finite satisfiability of C² with two linear orders is undecidable

Finite satisfiability is undecidable for two-variable logic with counting over structures with two linear orders, arbitrarily many unary predicates and two further binary predicates.

**Theorem (Charatonik and Witkowski).** The finite satisfiability problem for [C²](two-variable-logic-and-its-counting-extension.md) over signatures with two binary symbols $<_1$, $<_2$ interpreted as linear orders, any number of unary symbols and any number of further binary symbols is undecidable. It remains undecidable when at most two further binary symbols are allowed (the logic $\mathrm{C}^2(*, 2, \{<_1, <_2\})$).

In contrast, the same paper shows that with one linear order and its successor, and no other binary symbols, finite satisfiability of C² is NEXPTIME-complete, and that with one linear order and one more binary symbol it is decidable and as hard as emptiness of multicounter automata.

## Depends on

- [Two-variable logic and its counting extension](two-variable-logic-and-its-counting-extension.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Manuel proved that FO² over finite structures with two linear orders and their successor relations, and no other binary symbols, has an undecidable finite satisfiability problem. In C², a fresh binary symbol $s$ is forced to be the successor of $<_i$ by saying that $s \subseteq {<_i}$ and that every element except the least has exactly one $s$-predecessor and every element except the greatest exactly one $s$-successor (Lemma 3.1); in a finite structure this pins $s$ down. Replacing the two successors in Manuel's formulas by two such defined symbols gives a linear-time reduction to $\mathrm{C}^2(*, 2, \{<_1, <_2\})$ (Corollary 3.2).

## Sources

- W. Charatonik and P. Witkowski, "Two-variable logic with counting and a linear order", *Logical Methods in Computer Science* 12(2), Paper 8, 2016, doi:10.2168/LMCS-12(2:8)2016; read as arXiv:1604.06038v2, <https://arxiv.org/abs/1604.06038v2>: Corollary 3.3 of arXiv:1604.06038v2, with Lemma 3.1 and Corollary 3.2, and the result of Manuel recalled before Corollary 3.3.
