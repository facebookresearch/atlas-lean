# Maximal matching and MIS require Omega(min(Delta, log n / log log n)) deterministic rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. Maximal matchings and maximal independent sets cannot be computed in $o\bigl(\Delta + \log\log n / \log\log\log n\bigr)$ rounds by any randomized LOCAL algorithm, nor in $o\bigl(\Delta + \log n / \log\log n\bigr)$ rounds by any deterministic LOCAL algorithm. Since both problems can be solved in $O(\Delta + \log^* n)$ rounds, the dependence on $\Delta$ is optimal.

## Proof sketch

Define a family of relaxed matching problems parametrized by two integers $(x, y)$, where nodes may be matched, pointed to by up to $x$ unmatched neighbours, or have up to $y$ special labels. One application of the speedup theorem maps the $(x, y)$-problem to a problem that relaxes to the $(x+1, y + x)$-problem, so a $t$-round algorithm for maximal matching yields a $0$-round algorithm for the $(t, O(t^2))$-problem, which is impossible while $t \ll \Delta$. Tracking the failure probability under randomized round elimination gives the randomized bound, and running the same argument for deterministic algorithms with $\Delta$ chosen as a function of $n$ gives the deterministic one; MIS is handled through a closely related family of relaxed problems on the same bipartite instances.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Automatic speedup theorem for round elimination](automatic-speedup-theorem.md)
- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)

## Sources

- A. Balliu, S. Brandt, J. Hirvonen, D. Olivetti, M. Rabie, J. Suomela, "Lower Bounds for Maximal Matchings and Maximal Independent Sets", FOCS 2019; Journal of the ACM 68(5) (2021), arXiv:1901.02441.
