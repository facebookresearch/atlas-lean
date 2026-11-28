# Conservative extensions are undecidable in fragments containing two-variable logic

In every fragment of first-order logic that contains two-variable logic FO², it is undecidable whether one sentence conservatively extends another, and so are Σ-inseparability, Σ-entailment and strong Σ-entailment.

**Theorem (Jung, Lutz, Martel, Schneider and Wolter).** Let $F$ be any fragment of first-order logic that extends [two-variable logic](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md) $\mathrm{FO}^2$. Then the following problems for $F$ are undecidable: [conservative extensions, $\Sigma$-inseparability, $\Sigma$-entailment and strong $\Sigma$-entailment](conservative-extensions-and-sigma-entailment.md) (Theorem 8 of the source).

## Depends on

- [Conservative extensions and Σ-entailment in fragments of first-order logic](conservative-extensions-and-sigma-entailment.md)
- [Two-variable logic and its counting extension](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces a tiling problem that asks for a tiling of some rectangle, of any size, whose borders carry designated tiles; the reduction is given in the appendix of the source. A complete expansion links the undecidability of this bordered rectangle tiling problem, which is a variant of the tiling problem on main and has no page here.

## Sources

- Jean Christoph Jung, Carsten Lutz, Mauricio Martel, Thomas Schneider and Frank Wolter, "Conservative extensions in guarded and two-variable fragments", in *44th International Colloquium on Automata, Languages, and Programming (ICALP 2017)*, LIPIcs 80, 108:1–108:14, 2017, doi:[10.4230/LIPIcs.ICALP.2017.108](https://doi.org/10.4230/LIPIcs.ICALP.2017.108). Numbering of the version read, arXiv:1705.10115v1: Theorem 8, Section 3, and its proof in the appendix (Definition 18, the bordered tiling problem, and Lemmas 20 and 21).
