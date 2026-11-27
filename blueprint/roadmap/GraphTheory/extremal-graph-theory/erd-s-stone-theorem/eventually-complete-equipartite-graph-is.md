# Erdős–Stone theorem

For every $r \ge 1$, $t \ge 0$ and $\varepsilon > 0$ there is $n_0$ such that every simple graph on $n \ge n_0$ vertices with at least

$$\Big(1 - \frac{1}{r} + \varepsilon\Big)\frac{n^2}{2}$$

edges contains the complete $(r+1)$-partite graph $K_{r+1}(t)$ with $t$ vertices in each class.

This is the form "every $G(n, m)$ with $m \ge \big(\tfrac{d-2}{2(d-1)} + c\big) n^2$ contains $K_d(t)$", quoted from Erdős and Stone in the introduction of Bollobás, Erdős and Simonovits (1976), with $d = r + 1$ and $c = \varepsilon/2$, for fixed $t$. That paper also determines how fast $t$ can grow: $t$ of order $\log n/\log(1/c)$ is possible and, up to a constant factor depending on $d$, best possible.

Proof: set $\beta = 1 - 1/r + \varepsilon/2$ and delete vertices of small degree. The [deletion lemma](exists-subset-forall-le-deg-in.md) gives a vertex set $T$ on which every vertex has at least $\beta\lvert T\rvert$ neighbours. The potential $\Phi(T)$ is at least $\Phi(V) \ge (\varepsilon/2)n^2 - \beta n$ and at most $\lvert T\rvert^2$, so $\lvert T\rvert$ grows with $n$. The minimum-degree form of the Erdős–Stone theorem, with $\varepsilon/2$, then applies to the graph induced on $T$ once $\lvert T\rvert$ is large.

## Informally uses

- [Deletion of low-degree vertices](exists-subset-forall-le-deg-in.md): the reduction to the minimum-degree form.

## Background

- [Kővári–Sós–Turán bound](../kovari-sos-turan.md): the bipartite case $r = 1$ with an explicit bound; Bollobás, Erdős and Simonovits (1976) note that the base case of their induction also follows from it.
- [Turán density of complete graphs](../tur-n-density-of-complete-graphs/turan-density-complete-graph.md): the Turán threshold $(1 - 1/r)\, n^2/2$ above which the theorem applies.

## Sources

- P. Erdős and A. H. Stone, "On the structure of linear graphs", *Bull. Amer. Math. Soc.* 52 (1946), 1087–1091 (not consulted directly).
- B. Bollobás, P. Erdős and M. Simonovits, "On the structure of edge graphs II", *J. London Math. Soc. (2)* 12 (1976), 219–224, introduction and Theorem.
- J. Noel, *Extremal Combinatorics* lecture notes (version of 15 Nov 2026), extremalcombinatorics.com, Section 3.3: Lemma 3.3.12 (deletion) and the proof of Theorem 3.3.10.
