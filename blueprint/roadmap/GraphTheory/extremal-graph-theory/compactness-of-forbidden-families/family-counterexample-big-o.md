# Big-O form of the counterexample to extremal compactness

There are a nonempty finite family $\mathcal F$ of connected bipartite cyclic graphs and a real $c>0$ such that each member $F$ satisfies $\operatorname{ex}(n,F)\ge c n^{4/3}$ for sufficiently large $n$, but $\operatorname{ex}(n,\mathcal F)=O(n^{4/3-1/48})$. This same family is not compact, and the general compactness conjecture is false.

## Depends on

- [Extremal number and compactness of a forbidden family](extremal-number-of-a-forbidden-family.md)

## Proof depends on

- [Quantitative counterexample to extremal compactness](quantitative-compactness-counterexample.md)

## Proof outline

Take sixteenth roots of the extremal-number upper bound using nonnegativity, and retain the same witness family, lower constant, and noncompactness conclusions.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 10](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `compactnessCounterexample_bigO`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/J_CompactnessConjecture.lean#L72-L85)
