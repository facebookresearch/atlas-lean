# Graph databases and regular path queries

Let $G = (V, E)$ be a finite graph database with edges $E \subseteq V \times \Sigma \times V$, and let
the regular path query be given by a nondeterministic finite automaton $\mathcal{A}$ without
$\varepsilon$-transitions, with state set $Q$ and transition relation $\delta$. Costs are counted in the RAM model with
$G$ and $\mathcal{A}$ given by adjacency lists and labels compared in constant time. The answer is the set of pairs $(u, v)$ joined by a path whose label
word is accepted by $\mathcal{A}$. In the product graph with nodes $V \times Q$ and an edge from
$(u, p)$ to $(v, q)$ for each $(u, a, v) \in E$ and $(p, a, q) \in \delta$, $(u, v)$ is an answer if and
only if some node $(v, f)$ with $f$ final is reachable from some $(u, q_0)$ with $q_0$ initial.
Consequently, with $m = \lvert V \rvert \lvert Q \rvert + \lvert E \rvert \lvert \delta \rvert$:

1. deciding whether a given pair is an answer, and listing all answers with a given source $u$, take
   $O(m)$ time;
2. listing all answers takes $O(\lvert V \rvert \cdot m)$ time.

The all-pairs bound cannot be improved to $O(m)$ in general: on a directed cycle with $n$ nodes and all
edges labelled $a$, the query $a^*$ has $n^2$ answers. Regular path queries are expressible in linear
Datalog through the same product construction.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Sources

- Database Theory (summer semester 2025), International Center for Computational Logic, TU Dresden.
  <https://iccl.inf.tu-dresden.de/web/Database_Theory_(SS2025)> Background reference.
