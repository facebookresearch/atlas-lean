# Averaged fresh information across a finite-memory Gaussian block

There are absolute constants $C,C'>0$ and a natural $d_0$ such that the bounds below hold for every $d\ge d_0$, every natural $1\le m\le\lfloor d/8\rfloor$, and every choice of the finite singleton-measurable incoming and outgoing state spaces, joint law and transition kernel described next.

Start from any joint probability law $P$ of a uniform unit signal $S$ and a finite incoming state $U$. Draw $m$ independent fresh Gaussian rows $X$ and exact labels $XS$, and use any Markov transition kernel of $(U,X,XS)$ to a finite outgoing state $V$ (both singleton-measurable). For a signal-state law $Q$, let $I_k(Q)$ be [exposed information](conditional-information-from-marginal-kernels.md) with an independent $k$-row array, and let $\overline I(Q)$ be the average of its real projection for integer $k$ from $\lceil d/4\rceil$ to $\lfloor d/2\rfloor$ inclusive. Let $J$ be the number of those indices.

For any $B\ge0$ with $H(V)\le B$, the change from the incoming to outgoing signal-state law satisfies

$$
\Delta\overline I\le Cm+(m/J)(C+B/\lfloor d/8\rfloor)+B/\lfloor d/32\rfloor.
$$

If $B\le d^2$ the same change is at most $C'd$.

**Conventions.** Use the finite-state randomized block law, exact Gaussian labels, and average of the conditional informations over their closed natural width interval.

## Depends on

- [Conditional information from marginal kernels](conditional-information-from-marginal-kernels.md)
- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

The hybrid replacement comparison for changing the already seen rows to fresh rows and control of boundary widths in the average.

## Expansion

Use the joint law induced by the same transition kernel before and after each comparison. Track the width-averaging boundary terms, the entropy price for outgoing state, and the rounded dimensions, then specialize $B\le d^2$ for the coarser bound.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L511-L513)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
