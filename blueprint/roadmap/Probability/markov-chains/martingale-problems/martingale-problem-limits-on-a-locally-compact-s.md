# Martingale-problem limits on a locally compact state space

Let $E$ be a locally compact Polish space, $T>0$, and $\mathcal G$ a countable set of pairs $(f,Af)$ with $f\in C_c(E)$ and $Af$ bounded continuous, such that every pair of the graph of $A$ is the bounded-pointwise limit of a sequence in $\mathcal G$ ([countable core lemma](countable-bounded-pointwise-graph-core-for-marti.md)). Let $X^N$ be càdlàg processes in $E$ and $A_N$ operators such that:

1. for every $(f,Af)\in\mathcal G$, $f(X^N_t)-f(X^N_0)-\int_0^tA_Nf(X^N_s)\,ds$ is a martingale with respect to the natural filtration of $X^N$;
2. for every $(f,Af)\in\mathcal G$, $\sup_N\sup_{x\in E}|A_Nf(x)|<\infty$ and $\sup_{x\in K}|A_Nf(x)-Af(x)|\to0$ for every compact $K\subseteq E$;
3. $X^N_0\Rightarrow\mu$;
4. the laws of $X^N$ are C-tight in $D([0,T],E)$ and satisfy compact containment: for every $\eta>0$ there is a compact $K$ with $\inf_N\mathbb P(X^N_t\in K\text{ for all }t\le T)\ge1-\eta$ (as in the [Aldous criterion with compact containment](../../convergence-of-measures/skorokhod-space/aldous-tightness-criterion-in-d-0-t-e-with-initi.md)).

Then every subsequential limit in law $X$ has continuous paths and solves the $(A,\mu)$ [martingale problem](martingale-problems-generic-definition.md) on $[0,T]$ for the pairs of $\mathcal G$, hence, by the countable core lemma, for the whole graph of $A$.

The convergence in hypothesis 2 cannot be dropped: constant processes $X^N_t=x$ with $A_N=0$ satisfy 1, 3 and 4 but, for the target $Af=\tfrac12f''$, not the convergence in 2, and the constant limit does not solve the martingale problem for $\tfrac12f''$.

## Depends on

- [A countable bounded-pointwise core of the graph suffices for a martingale problem](countable-bounded-pointwise-graph-core-for-marti.md)
- [Aldous tightness criterion in D([0,T],E) with initial and compact-containment conditions](../../convergence-of-measures/skorokhod-space/aldous-tightness-criterion-in-d-0-t-e-with-initi.md)
- [Martingale problems](martingale-problems-generic-definition.md)

## Proof depends on

- [Limits of rescaled Markov chains solve the limit martingale problem](existence-by-approximation-limits-of-chains-solv.md)

## Expansion

A full proof page must establish:

- Replacing $A_Nf$ by $Af$ inside $\mathbb E\bigl[(f(X^N_t)-f(X^N_s)-\int_s^tA_Nf(X^N_u)\,du)H\bigr]$: on the compact-containment event the error is at most $(t-s)\sup_K|A_Nf-Af|$, and off it at most $(t-s)\bigl(\sup_N\lVert A_Nf\rVert_\infty+\lVert Af\rVert_\infty\bigr)\eta\lVert H\rVert_\infty$.
- Passage to the limit along the subsequence, using continuity of the limit paths, as in [the approximation theorem on a compact space](existence-by-approximation-limits-of-chains-solv.md); a monotone-class step to the natural filtration.
- The constant-process guard.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4.
