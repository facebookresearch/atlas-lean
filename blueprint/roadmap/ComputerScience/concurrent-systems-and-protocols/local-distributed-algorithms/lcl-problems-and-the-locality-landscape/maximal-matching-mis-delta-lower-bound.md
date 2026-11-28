# Maximal matching and MIS require Omega(min(Delta, log n / log log n)) deterministic rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. Every randomized LOCAL algorithm that finds a maximal matching, or a maximal independent set, on all graphs of maximum degree at most $\Delta$ with probability at least $1 - 1/n$ needs $\Omega\bigl(\min\{\Delta, \log\log n / \log\log\log n\}\bigr)$ rounds, and every deterministic LOCAL algorithm needs $\Omega\bigl(\min\{\Delta, \log n / \log\log n\}\bigr)$ rounds. Since both problems can be solved in $O(\Delta + \log^* n)$ rounds, the dependence on $\Delta$ is optimal.

## Proof sketch

Work on $2$-coloured $\Delta$-regular trees (high-girth regular graphs locally) and define a family $\Pi_\Delta(x, y)$ of relaxed matching problems, where $\Pi_\Delta(0, 0)$ is maximal matching and larger $x$ or $y$ make the problem easier. For $\Delta \ge 2x + y + 1$, one round-elimination step turns a $T$-round algorithm for $\Pi_\Delta(x, y)$ into a $(T-1)$-round algorithm for $\Pi_\Delta(x+1, y+x)$; with randomness, a local error probability $p \le 1/4^{\Delta+1}$ becomes at most $5\Delta p^{1/(\Delta+1)}$. The condition $\Delta \ge 2x + y + 1$ prevents iterating from $(0, 0)$ for $t$ of order $\Delta$, since $y$ grows quadratically. Instead start from a $k$-matching with $k = \Theta(\sqrt\Delta)$, which yields $\Pi_\Delta(k - 1, 0)$: after $T \le \sqrt\Delta/16$ steps one reaches $x, y \le \Delta/8$, a problem with no $0$-round solution beyond a small error, so $O(\sqrt\Delta)$-matchings need $\Omega(\sqrt\Delta)$ rounds. Splitting every vertex into $O(\sqrt\Delta)$ virtual vertices of degree $O(\sqrt\Delta)$ turns a maximal matching algorithm with $o(\Delta)$ rounds into an $O(\sqrt\Delta)$-matching algorithm with $o(\sqrt\Delta)$ rounds, giving $\Omega(\Delta)$; tracking the error on graphs whose neighbourhoods are trees up to radius $\Theta(\log_\Delta n)$ gives the randomized bound $\Omega(\min\{\Delta, \log_\Delta \log n\})$. A deterministic algorithm with fewer than $c \min\{\Delta, \log_\Delta n\}$ rounds on $N$-vertex graphs is simulated on $2^N$-vertex graphs with identifiers replaced by a colouring of a power graph computed by Linial's colour reduction, contradicting the randomized bound. For MIS, an MIS algorithm run on the line graph finds a maximal matching, with constant overhead in rounds and a constant-factor increase in maximum degree; these line-graph instances are not the bipartite matching instances above.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Automatic speedup theorem for round elimination](automatic-speedup-theorem.md)
- [Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds](../deterministic-colouring-and-mis-in-local-and-congest/linial-colour-reduction.md)

## Sources

- A. Balliu, S. Brandt, J. Hirvonen, D. Olivetti, M. Rabie, J. Suomela, "Lower Bounds for Maximal Matchings and Maximal Independent Sets", FOCS 2019; Journal of the ACM 68(5) (2021), arXiv:1901.02441, Lemmas 3.1, 3.5 and 4.1, Theorems 3.7, 4.10 and 4.13, and Corollaries 4.11, 4.15, 4.16 and 4.17.
