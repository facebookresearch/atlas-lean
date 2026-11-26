# The extremal compactness conjecture is false

It is not true that every nonempty finite family of cyclic finite simple graphs is compact. Equivalently there is such a family $\mathcal F$ for which no member $F\in\mathcal F$ has $\operatorname{ex}(n,F)=O(\operatorname{ex}(n,\mathcal F))$ as $n\to\infty$. This is the negative answer to Erdős Problem 180.

## Depends on

- [Extremal number and compactness of a forbidden family](extremal-number-of-a-forbidden-family.md)

## Proof depends on

- [Quantitative counterexample to extremal compactness](quantitative-compactness-counterexample.md)

## Proof outline

Extract the noncompact witness from the quantitative result; its members being connected and bipartite are extra properties of the witness, not restrictions in the universal claim that is negated.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 10](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Erdős Problem 180](https://www.erdosproblems.com/180)
- [Pinned source: `not_erdos_180`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/J_CompactnessConjecture.lean#L46-L47)
