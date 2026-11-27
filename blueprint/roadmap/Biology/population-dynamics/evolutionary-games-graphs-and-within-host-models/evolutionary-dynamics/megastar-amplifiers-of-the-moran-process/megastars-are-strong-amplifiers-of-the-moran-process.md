# Megastars are strong amplifiers of the Moran process

**Setting.** Let $G$ be a strongly connected directed graph on $n$ vertices. In the Moran process on $G$ every vertex is either a mutant of fitness $r > 1$ or a non-mutant of fitness $1$. At each step an individual is chosen with probability proportional to its fitness and copies its type onto an out-neighbour chosen uniformly at random. Started from a single mutant placed uniformly at random, the process a.s. reaches fixation (all mutants) or extinction (no mutants).

**Amplification.** For a function $f : \mathbb{R}_{>1} \times \mathbb{Z}_{\ge 1} \to \mathbb{R}_{\ge 0}$, an infinite family $\Upsilon$ of directed graphs is *up-to-$f$ fixating* if for every $r > 1$ there is $n_0(r)$ such that every $G \in \Upsilon$ with $n \ge n_0$ vertices has extinction probability at most $f(r, n)$ from a uniformly random initial mutant. The family is *amplifying* if this holds with $\lim_{n\to\infty} f(r,n) < 1/r$ for every $r > 1$ (the limiting extinction probability of the complete graph is $1/r$), and *strongly amplifying* if it holds with $\lim_{n\to\infty} f(r,n) = 0$ for every $r > 1$.

**Megastar.** For positive integers $k, \ell, m$ the $(k,\ell,m)$-megastar has as vertices $\ell$ reservoirs $R_1, \dots, R_\ell$ of size $m$, $\ell$ cliques $K_1, \dots, K_\ell$ of size $k$, $\ell$ feeder vertices $a_1, \dots, a_\ell$ and a centre $v^*$, so $n = \ell(m + k + 1) + 1$. Its edges are: $v^* \to$ every reservoir vertex; every vertex of $R_i$ $\to a_i$; $a_i \to$ every vertex of $K_i$; both directions between distinct vertices of $K_i$; every clique vertex $\to v^*$.

**Theorem (strong amplification with optimal polynomial rate).** Let $m(\ell) = \ell$, $k(\ell) = \lceil (\log \ell)^{23} \rceil$ and $\Upsilon_{\mathcal M} = \{(k(\ell), \ell, m(\ell))\text{-megastar} : \ell \ge 2\}$.

1. $\Upsilon_{\mathcal M}$ is up-to-$f$ fixating for $f(r,n) = (\log n)^{23} n^{-1/2}$; in particular $\Upsilon_{\mathcal M}$ is strongly amplifying.
2. Conversely, no infinite family of megastars (any parameters) is up-to-$f$ fixating for $f(r,n) = n^{-1/2}/(52 r^2)$.

So the extinction probability of the best megastars decays like $n^{-1/2}$ up to a polylogarithmic factor, and no megastar does better.

## Depends on

- [Moran fixation probability](../../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)

## Expansion

The design replaces the path linking each reservoir of a superstar to the centre by a feeder vertex and a clique. A mutant born in a reservoir is almost surely the initial one (reservoirs hold most vertices); it repeatedly spawns onto the feeder, which seeds the clique, and inside a clique of size $k$ a mutant population behaves like a biased random walk with drift $r$, so the clique fills with mutants with probability bounded away from zero and then fires many mutants into $v^*$, which refills reservoirs. The $(\log n)^{23}$ factor comes from the concentration arguments (Poisson and gambler's-ruin bounds) that control clock triggers in each time window. The lower bound (the fixation probability of any megastar is at most $1 - 1/(52 r^2 \sqrt{n})$) is a three-case argument: for $n \le 144 r^2$ the initial mutant dies before reproducing with probability at least $1/(2rn)$; if $m \le k\sqrt{n}$ the mutant lands in a clique with probability of order $k/(m+k)$ and is overwritten first; otherwise $\ell \le \sqrt{n}$, and a reservoir mutant is overwritten by $v^*$ before its offspring at the feeder survive, with probability at least $1/(26 r^2 \ell)$.

## Sources

- Andreas Galanis, Andreas Göbel, Leslie Ann Goldberg, John Lapinskas and David Richerby, "Amplifiers for the Moran Process", arXiv:1512.05632 (2015): Definitions 1–3 (up-to-$f$ fixating, amplifying, strongly amplifying), Section 1.1 (megastar definition), Theorem 4, Definition 5, Theorem 6, Corollary 7, Theorem 11 and its quantitative form Theorem 127 (fixation probability at most $1 - 1/(52r^2\sqrt{n})$) with Lemmas 125–126 (Section 7). <https://doi.org/10.48550/arXiv.1512.05632> Published version: Journal of the ACM 64 (2017) 1–90, <https://doi.org/10.1145/3019609>.
