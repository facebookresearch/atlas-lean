# Exponential decay of the cluster volume

For Bernoulli bond percolation on $\mathbb{Z}^d$ with $d \ge 2$ and every $p < p_c(d)$, there are $c, C > 0$ such that for every $n \in \mathbb{N}$,

$$\mathbb{P}_p\big(|C(0)| \ge n\big) \le C e^{-cn},$$

where $C(0)$ is the open cluster of the origin and an infinite cluster counts as having at least $n$ sites. The source writes the bound as $e^{-c'_p n}$ for every $n$; at $n = 1$ the left side is $1$, so this version carries a prefactor $C$.

## Informally uses

- [Exponential decay below $p_c$](../sharpness-of-the-phase-transition-for-bernoulli/cross-prob-exp-decay-of-lt-pc.md): the input of the source's coarse-graining proof (Theorem 3.3 there).

## Background

- [Finite susceptibility below $p_c$](../sharpness-of-the-phase-transition-for-bernoulli/summable-conn-prob-of-lt-pc.md): the weaker statement that the expected cluster volume is finite.

## Sources

- Hugo Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of 7 October 2018), Theorem 3.7, proved there by coarse graining from exponential decay of the radius (Theorem 3.3).
