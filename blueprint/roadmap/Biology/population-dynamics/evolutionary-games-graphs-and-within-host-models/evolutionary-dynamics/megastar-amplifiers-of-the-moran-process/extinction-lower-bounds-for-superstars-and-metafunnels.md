# Extinction lower bounds for superstars and metafunnels

**Setting.** The Moran process with mutant fitness $r > 1$ on a directed graph $G$ with $n$ vertices, started from one uniformly random mutant; a family of graphs is *up-to-$f$ fixating* if for each $r > 1$ all large enough members have extinction probability at most $f(r,n)$ (see [Megastars are strong amplifiers of the Moran process](megastars-are-strong-amplifiers-of-the-moran-process.md)).

**Superstar.** For positive integers $k, \ell, m$ the $(k,\ell,m)$-superstar has $\ell$ reservoirs $R_1, \dots, R_\ell$ of size $m$, $\ell$ paths $v_{i,1} \cdots v_{i,k}$ and a centre $v^*$, with edges $v^* \to R_i$ (all vertices), $R_i \to v_{i,1}$, $v_{i,j} \to v_{i,j+1}$ for $j < k$, and $v_{i,k} \to v^*$.

**Metafunnel.** The $(k,\ell,m)$-metafunnel has a centre $v^*$ and, for $i \in [k]$, levels $V_i = V_{i,1} \sqcup \dots \sqcup V_{i,\ell}$ with $|V_{i,j}| = m^i$; its edges are $V_0 \times V_k$ (with $V_0 = \{v^*\}$), $V_1 \times V_0$, and $V_{i+1,j} \times V_{i,j}$ for $i \in [k-1]$, $j \in [\ell]$.

**Theorem.**

1. *(Superstars.)* For every $r > 1$ there is $c_r > 0$ such that for all $k, \ell, m$ the extinction probability on the $(k,\ell,m)$-superstar is at least $1/(c_r (n \log n)^{1/3})$. Hence if $\lim_{n\to\infty} f(r,n)\,(n \log n)^{1/3} = 0$ for every $r > 1$, no infinite family of superstars is up-to-$f$ fixating.
2. *(Metafunnels.)* For every fixed $\delta > 0$, no infinite family of metafunnels is up-to-$f$ fixating with $f(r,n) = n^{-\delta}$; more strongly, for every fixed $\epsilon < 1/2$, none is up-to-$f$ fixating with $f(r,n) = n^{-1/(\log n)^{\epsilon}}$.

Superstars may still be strongly amplifying, but their extinction probability cannot decay faster than $(n \log n)^{-1/3}$, and metafunnels cannot reach any polynomial rate; megastars reach $n^{-1/2}$ up to polylogarithmic factors, so they are provably better amplifiers than both earlier families.

## Depends on

- [Megastars are strong amplifiers of the Moran process](megastars-are-strong-amplifiers-of-the-moran-process.md)

## Expansion

For superstars, two easy extinction events already give polynomial lower bounds: a uniformly placed mutant is overwritten before it reproduces with probability at least $k/(2r(m+k))$, and, when $m \ge 12r$, a mutant in a reservoir is overwritten by $v^*$ before its offspring cross the path with probability at least $1/(26 r^2 \ell)$. The remaining regime (long reservoirs feeding many paths) is handled by showing that the path of the initial mutant's reservoir does not clear and fill with mutants within time windows of length $\kappa = \max\{3k, 70 r^4 \log n\}$; optimizing over $(k,\ell,m)$ with $n \approx \ell(m+k)$ yields the $(n \log n)^{-1/3}$ barrier.

## Sources

- Andreas Galanis, Andreas Göbel, Leslie Ann Goldberg, John Lapinskas and David Richerby, "Amplifiers for the Moran Process", arXiv:1512.05632 (2015): Section 1.1 (metafunnel and superstar definitions), Theorems 8, 9 and 10; Section 4 (upper bound on the fixation probability of superstars): Theorem 29, Lemmas 30 and 31, Definition 32. <https://doi.org/10.48550/arXiv.1512.05632> Published version: Journal of the ACM 64 (2017) 1–90, <https://doi.org/10.1145/3019609>.
