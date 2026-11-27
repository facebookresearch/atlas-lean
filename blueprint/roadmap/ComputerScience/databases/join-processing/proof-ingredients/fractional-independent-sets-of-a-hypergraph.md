# Fractional independent sets of a hypergraph

Let $H = (V, E)$ be a hypergraph. An *independent set* of $H$ is a set $V' \subseteq V$ with $|e \cap V'| \le 1$ for every
edge $e \in E$. A *fractional independent set* of $H$ is a function $g : V \to \mathbb Q_{\ge 0}$ with $\sum_{v \in e} g(v) \le 1$ for
every edge $e \in E$; its weight is $\sum_{v \in V} g(v)$. A fractional independent set is *maximal* when its weight is the
largest possible, the optimal value of the linear program that maximizes $\sum_v g(v)$ under these constraints. For the
triangle query $R[A, B] \bowtie S[B, C] \bowtie T[C, A]$, the function with value $1/2$ on every attribute is a maximal
fractional independent set of weight $3/2$.

## Depends on

- [Natural join queries, their hypergraphs and fractional edge covers](../natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 25.4 and 25.12, Example 25.13 and the linear program $IS(H_q)$ (pp. 209–220).
