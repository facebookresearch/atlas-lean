# Tightness in $D([0,T],E)$ from compact containment and the modulus $w'$

Let $(E,r)$ be a complete separable metric space, $T>0$, and for $x\in D([0,T],E)$ and $\delta>0$ let

$$w'(x,\delta)=\inf\ \max_{1\le i\le m}\ \sup_{s,t\in[t_{i-1},t_i)}r\bigl(x(s),x(t)\bigr),$$

the infimum over all partitions $0=t_0<t_1<\cdots<t_m=T$ with $t_i-t_{i-1}>\delta$ for every $i$. For each $n$ let $X^n$ be a random element of the [Skorokhod space](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md) $D([0,T],E)$. Suppose

1. compact containment: for every $\varepsilon>0$ there is a compact $K\subseteq E$ with $\mathbb P\bigl(X^n_t\in K\text{ for all }t\le T\bigr)\ge1-\varepsilon$ for every $n$;
2. for every $\eta>0$, $\displaystyle\lim_{\delta\to0}\limsup_{n\to\infty}\mathbb P\bigl(w'(X^n,\delta)\ge\eta\bigr)=0$.

Then the laws of $X^n$ are tight in $D([0,T],E)$ with the J1 topology.

## Depends on

- [Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md)

## Expansion

A proof page must establish the characterization of relatively compact subsets of $D([0,T],E)$: a set $A$ has compact closure if there is a compact $K\subseteq E$ containing all values of the paths in $A$ and $\lim_{\delta\to0}\sup_{x\in A}w'(x,\delta)=0$; replace the $\limsup$ in condition 2 by a supremum over $n$, since each single law is tight and $w'(x,\delta)\to0$ for every càdlàg $x$; and assemble a compact set of uniformly large probability from countably many choices of $\delta$. It should fix the convention at the terminal time used in the definition of $w'$, which differs between the sources.

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Chapter 3, Section 13.
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, Chapter 3, Sections 6 and 7.
