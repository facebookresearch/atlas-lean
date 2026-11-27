# Conservative extensions are undecidable in fragments containing the three-variable guarded fragment

In every fragment of first-order logic that contains the three-variable guarded fragment, it is undecidable whether one sentence conservatively extends another, and so are Σ-inseparability, Σ-entailment and strong Σ-entailment.

**Theorem (Jung, Lutz, Martel, Schneider and Wolter).** Let $F$ be any fragment of first-order logic that extends the three-variable [guarded fragment](../guarded-and-fluted-fragments/guarded-fragment.md) $\mathrm{GF}^3$. Then the following problems for $F$ are undecidable: [conservative extensions, $\Sigma$-inseparability, $\Sigma$-entailment and strong $\Sigma$-entailment](conservative-extensions-and-sigma-entailment.md) (Theorem 7 of the source).

The source notes that the proof gives witnesses in the two-variable guarded fragment, so $\mathrm{GF}^2$-conservative extensions of $\mathrm{GF}^3$-sentences are already undecidable. In contrast, conservative extensions are decidable and 2ExpTime-complete in the two-variable guarded fragment $\mathrm{GF}^2$, the intersection of $\mathrm{GF}$ and $\mathrm{FO}^2$.

## Depends on

- [Conservative extensions and Σ-entailment in fragments of first-order logic](conservative-extensions-and-sigma-entailment.md)
- [Guarded fragment of first-order logic](../guarded-and-fluted-fragments/guarded-fragment.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

From a two-register machine $M$ the proof builds $\mathrm{GF}^3$-sentences $\varphi_1$ and $\varphi_2$ such that $M$ halts on input $(0, 0)$ if and only if $\varphi_1 \wedge \varphi_2$ is not a conservative extension of $\varphi_1$ (Lemma 6 of the source): $\varphi_1$ describes configurations linked by a successor relation with register contents encoded by path lengths, and $\varphi_2$ forces a defect whenever a halting computation is represented. Undecidability of halting for two-register machines transfers to conservative extensions, and from there to the other three problems.

## Sources

- Jean Christoph Jung, Carsten Lutz, Mauricio Martel, Thomas Schneider and Frank Wolter, "Conservative extensions in guarded and two-variable fragments", in *44th International Colloquium on Automata, Languages, and Programming (ICALP 2017)*, LIPIcs 80, 108:1–108:14, 2017, doi:[10.4230/LIPIcs.ICALP.2017.108](https://doi.org/10.4230/LIPIcs.ICALP.2017.108). Numbering of the version read, arXiv:1705.10115v1: Theorem 7 and Lemma 6, Section 3.
