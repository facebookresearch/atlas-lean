# Almost-sure limit of the scaled cophenetic index of the Yule tree

Let $\mathcal{T}_n$ be a Yule (pure-birth) tree with speciation rate $\lambda=1$, conditioned on $n$ contemporary tips and including the root edge from the origin. For tips $i\ne j$ let $\phi^{(n)}_{ij}$ be the time from the origin to the most recent common ancestor of $i$ and $j$, and define the **continuous cophenetic index**

$$\Phi^{(n)} = \sum_{1\le i<j\le n}\phi^{(n)}_{ij}, \qquad W_n = \binom{n}{2}^{-1}\Phi^{(n)}.$$

The discrete version $\tilde\Phi^{(n)}$ counts edges instead of time (the total cophenetic index of the tree shape), with $\tilde W_n=\binom{n}{2}^{-1}\tilde\Phi^{(n)}$.

**Theorem.**

1. $(W_n)_{n\ge2}$ is a positive submartingale (with respect to the tree-growth filtration) that converges almost surely and in $L^2$ to a random variable $W_\infty$ with finite first and second moments.
2. $(\tilde W_n)_{n\ge2}$ is likewise a submartingale converging almost surely and in $L^2$.
3. $W_n = \sum_{i=1}^{n-1} V_i^{(n)} Z_i$, where $Z_1,\dots,Z_{n-1}$ are i.i.d. $\mathrm{Exp}(1)$ (the scaled inter-speciation times) and the weights $V_i^{(n)}$ depend only on the tree shape.
4. With $H_{n,1}=\sum_{k=1}^n 1/k$,

$$\mathbb{E}\bigl[\Phi^{(n)}\bigr] = \binom{n}{2}\frac{2\,(n-H_{n,1})}{n-1}\sim n^2, \qquad \mathrm{Var}\bigl[\Phi^{(n)}\bigr]\sim\frac{2\pi^2-9}{36}\,n^4,$$

and removing the root edge subtracts $\binom{n}{2}$ from the mean, since $\Phi^{(n)}=\Phi^{(n)}_{\mathrm{NRE}}+\binom{n}{2}T_1$ with $T_1\sim\mathrm{Exp}(1)$.

Without branch lengths the limit of the centered discrete index is the fixed point of a Quicksort-type contraction: splitting the tips at the root by a uniform proportion $\tau$, the limit law $Y$ satisfies $Y\overset{d}{=}\tau^2Y+(1-\tau)^2Y'+\tfrac12-3\tau(1-\tau)$ with $Y,Y',\tau$ independent. Quantiles of these limits give a test of whether an observed tree is consistent with the pure-birth model.

## Expansion

1. Under the Yule process, between the $k$th and $(k+1)$st speciation all $k$ lineages extend by an $\mathrm{Exp}(k)$ time, which adds that time to $\phi_{ij}$ for every pair not yet split; this gives the representation in item 3.
2. Adding a tip increases $\binom{n}{2}$ and the sum by comparable amounts, and conditioning on the past shows $\mathbb{E}[W_{n+1}\mid\mathcal{F}_n]\ge W_n$.
3. The exact second moment is bounded uniformly in $n$ (item 4 gives $\mathrm{Var}\,W_n\to(2\pi^2-9)/9$), so the $L^2$-bounded submartingale converges almost surely and in $L^2$.
4. In the discrete case the root split of a Yule tree shape is uniform, which yields the contraction recursion.

## Sources

- K. Bartoszek, *Exact and approximate limit behaviour of the Yule tree's cophenetic index*, arXiv:1703.08954 (Theorems 2.4, 2.7, 2.11, 2.12 and Section 3). <https://doi.org/10.48550/arXiv.1703.08954> Published version: Mathematical Biosciences 303:26-45, 2018, <https://doi.org/10.1016/j.mbs.2018.05.005>.
