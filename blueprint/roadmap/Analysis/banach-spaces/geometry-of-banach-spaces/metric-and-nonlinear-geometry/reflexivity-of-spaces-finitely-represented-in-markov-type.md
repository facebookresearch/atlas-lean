# Reflexivity of Banach spaces finitely representable in a space of nontrivial Markov type

Let $X$ be a real normed space, not required complete, and $Y$ a complete real normed space; their underlying types can be in different universes. Assume $X$ has nontrivial Markov type: some real $p>1$ and $K>0$ work in the inequality

$$
\mathbb E\|f(Z_n)-f(Z_0)\|^p\le K^p n\,\mathbb E\|f(Z_1)-f(Z_0)\|^p
$$

for every finite chain, every state map $f$ into $X$, and every positive natural time $n$. A chain is specified by a nonnegative probability vector $\pi$ and nonnegative row-stochastic matrix $P$ satisfying detailed balance $\pi_iP_{ij}=\pi_jP_{ji}$, with path probabilities $\pi_{z_0}\prod_{j<n}P_{z_jz_{j+1}}$. Zero-mass states are allowed.

Suppose that for every finite-dimensional real linear subspace $E\subseteq Y$ and every real $\eta>0$, there exists a linear map $T:E\to X$ with $\|z\|\le\|Tz\|\le(1+\eta)\|z\|$ for every $z\in E$. Then the canonical map $Y\to Y^{**}$ onto the continuous bidual is surjective. This is finite representability of $Y$ **in** $X$, not the reverse condition; neither space must be nonzero.

## Depends on

Finite reversible path expectation, near-isometric representations of finite-dimensional subspaces and the canonical map to the continuous bidual.

## Proof depends on

The construction of an ordered finite-coordinate norm from failure of reflexivity in a finitely representable space, and the independent Markov-chain obstruction to representing that ordered norm when $p>1$.

## Expansion

Build the ordered-norm construction starting from non-surjectivity of the bidual map. Show its finite-coordinate representability transfers through the prescribed almost-isometric linear maps, then apply the reversible-chain obstruction. Completeness is only assumed for $Y$.

## Sources

- OpenAI Math, [`finitelyRepresentable_reflexive`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/MarkovReflexivity.lean#L22-L24).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/327.md).
- [Definitions in `FiniteChains.lean`, lines 14–43](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/FiniteChains.lean#L14-L43).
- [Definitions in `FinitelyRepresentable.lean`, lines 10–21](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/FinitelyRepresentable.lean#L10-L21).
- [Definitions in `MarkovReflexivity.lean`, lines 9–20](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/MarkovReflexivity.lean#L9-L20).
