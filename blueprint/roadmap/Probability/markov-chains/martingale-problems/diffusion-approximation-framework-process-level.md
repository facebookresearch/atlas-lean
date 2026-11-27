# Diffusion approximation: tightness and a well-posed limit martingale problem give process-level convergence

Let $E$ be a compact metric space and $T>0$. For each $N$ let $(Y^N_k)_{k\ge0}$ be an $E_N$-valued Markov chain, $E_N\subseteq E$, and define the rescaled process

$$X^N_t=Y^N_{\lfloor tM_N\rfloor},\qquad 0\le t\le T,$$

with a time scale $M_N\to\infty$ (generations per unit of time; any state scaling is built into the embedding $E_N\subseteq E$). Let $A$ be an operator with $\mathcal D(A)\subseteq C(E)$ and $\mu$ a probability measure on $E$. Assume:

1. the laws of $X^N$ in the [Skorokhod space](../../convergence-of-measures/skorokhod-space/skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md) $D([0,T],E)$ are tight, and $X^N_0\Rightarrow\mu$;
2. every subsequential limit in law of $(X^N)$ solves the $(A,\mu)$ [martingale problem](martingale-problems-generic-definition.md) on $[0,T]$;
3. the $(A,\mu)$ martingale problem has at most one solution in $D([0,T],E)$ (in law), for instance by [duality](uniqueness-of-martingale-problems-by-duality.md).

Then $X^N\Rightarrow X$ in $D([0,T],E)$, where $X$ is the unique solution. If the laws of $X^N$ are C-tight, $X$ has continuous paths.

For the neutral haploid Wright–Fisher chain with $M$ gene copies, state the allele frequency in $\{0,1/M,\ldots,1\}\subseteq[0,1]$ and time scale $M_N=M$, the one-generation conditional variance $x(1-x)/M$ and zero mean change identify the limit generator $Af=\tfrac12x(1-x)f''$.

## Depends on

- [Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings](../../convergence-of-measures/skorokhod-space/skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md)
- [Martingale problems](martingale-problems-generic-definition.md)

## Proof depends on

- [Prokhorov's theorem, sequential form on $\mathbb{R}$](../../convergence-of-measures/prokhorov-theorem/prokhorov-sequential.md)
- [Skorokhod space D[0,T] with J1 metric](../../convergence-of-measures/skorokhod-space/skorokhod-space-d-0-t-with-j1-metric.md)
- [D([0,T],E) is Polish for Polish E](../../convergence-of-measures/skorokhod-space/d-0-t-e-is-polish-for-polish-e.md)
- [Borel sigma-algebra of D equals the coordinate sigma-algebra; fdd determine laws](../../convergence-of-measures/skorokhod-space/borel-sigma-algebra-of-d-equals-the-coordinate-s.md)

## Expansion

A full proof page must establish:

- Prokhorov's theorem on the Polish space $D([0,T],E)$: tightness gives relative compactness, so every subsequence has a further convergent subsequence.
- Every subsequential limit has the same law, by hypotheses 2 and 3 and because finite-dimensional distributions determine laws on $D$; hence the whole sequence converges.
- C-tightness implies continuity of the limit paths.
- The Wright–Fisher normalization check, including that a time unit of $M$ generations gives the factor $\tfrac12$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4 (convergence via martingale problems).
