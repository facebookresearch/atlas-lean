# Nontrivial Markov type and uniformly convex renorming

Let $X$ be a real Banach space, possibly the zero space. For a finite state set $S$, let $\pi$ be a probability vector and $P$ a nonnegative row-stochastic matrix satisfying $\pi_iP_{ij}=\pi_jP_{ji}$. The path $(s_0,\ldots,s_n)$ has weight $\pi_{s_0}\prod_{i<n}P_{s_i s_{i+1}}$. Say $X$ has nontrivial Markov type if there are real $p>1$ and $K>0$ such that for all these chains, all maps $f:S\to X$ and all integers $n\ge1$,

$$\mathbb E\|f(s_n)-f(s_0)\|^p\le K^p n\,\mathbb E\|f(s_1)-f(s_0)\|^p.$$

This holds if and only if $X$ admits a real seminorm $N$ with $a\|x\|\le N(x)\le b\|x\|$ for $a,b>0$, which is uniformly convex: for every $0<\epsilon\le2$ some $\delta>0$ satisfies $N((x+y)/2)\le1-\delta$ whenever $N(x),N(y)\le1$ and $N(x-y)\ge\epsilon$.

## Depends on

- Finite reversible path weights and the equivalence bounds for an auxiliary norm, as specified above.

## Proof depends on

- Uniform reversible-chain bounds for the renormed space and a construction of a uniformly convex equivalent norm from a nontrivial bound on all such chains.

## Expansion

Formalize path expectation including states of zero stationary mass, prove invariance under norm equivalence, then separate the two directions. Neither a chain-dependent constant nor a single-time estimate suffices.

## Sources

- OpenAI, [MarkovType comparator, hasNontrivialMarkovType_iff_hasEquivalentUCNorm](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MarkovType.lean#L71-L74).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/327.md).
