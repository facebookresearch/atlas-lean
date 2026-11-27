# Existence of a finitely presented nonsofic group

There is a finitely presented group which is not sofic in the following permutation-approximation sense. A group $G$ is sofic if for every finite $F\subseteq G$ and every $0<\varepsilon<1$ there are $n\ge1$ and a map $\phi:G\to S_n$ with $\phi(1)=1$ such that for all $g,h\in F$,

$$d(\phi(gh),\phi(g)\phi(h))<\varepsilon,$$

and for every $g\in F\setminus\{1\}$, $d(\phi(g),1)>1-\varepsilon$. Here $d$ is the fraction of points where two permutations differ. The product condition does not require $gh\in F$ because the map is defined on all of $G$.

## Background

- [Sofic groups](is-sofic.md) uses a finite-domain formulation with an exact fixed-point-free test. The distance condition stated here is different; the link does not assert equivalence.

## Expansion

Build the finite-presentation and nonsoficity witnesses, and justify a bridge to any alternative formulation before using the result there. In particular the Kourovka predicate asks for exact fixed-point-free separation on its finite domain; approximate separation at an arbitrary small tolerance does not by itself give that clause.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 3](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned permutation model](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/D_NonSoficGroup.lean#L7-L26)
- [Pinned source: `exists_finitelyPresented_nonsofic_group`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/D_NonSoficGroup.lean#L30-L32)
