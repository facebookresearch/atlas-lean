# Nonatomic routing instance

A nonatomic routing instance consists of a finite set $E$ of edges, a set of commodities, a
finite set $\mathcal P$ of paths, each path $P$ belonging to a commodity $i(P)$ and using a
finite set of edges, and a latency function $\ell_e : \mathbb R \to \mathbb R$ for each edge
$e$, giving the delay of every unit of traffic on $e$ as a function of the total flow on $e$.

In a directed graph with source–sink pairs $(s_i, t_i)$, $\mathcal P$ is the set of simple
$s_i$–$t_i$ paths. Since an instance only records which edges each path uses, it also covers
the nonatomic congestion games of Roughgarden and Tardos (2004), where a strategy is any set of
resources.

## Background

- [Max-flow min-cut theorem](../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/README.md): background; a routing instance with one commodity and
  constant latencies is a flow problem, and a feasible path flow is a decomposition of an
  $s$–$t$ flow into paths.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, §2.1.
- T. Roughgarden and É. Tardos, "Bounding the inefficiency of equilibria in nonatomic congestion
  games", Games Econom. Behav. 47 (2004), 389–403.
