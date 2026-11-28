# Minimal realizations are exactly the canonical ones

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $\mathcal{A} = (\mathcal{A}_i)_{i \ge 1}$ be a Markov sequence in $\mathbb{K}^{p \times m}$, realized by triples $(A, B, C)$ of dimension $n \ge 0$ as in [Hankel factorization of Markov parameters](hankel-factorization-of-markov-parameters.md) (for $n = 0$ the triple is empty and realizes only the zero sequence). A realization is **canonical** if it is controllable and observable, $\operatorname{rank} R(A, B) = n$ and $\operatorname{rank} O(A, C) = n$, and **minimal** if every realization of $\mathcal{A}$ has dimension at least $n$. Then:

1. if $\mathcal{A}$ has a realization, it has a canonical realization;
2. a realization of $\mathcal{A}$ is minimal if and only if it is canonical.

For the discrete-time system $x^+ = A x + B u$, $y = C x$, the Markov parameters are its impulse response: the zero-state output to a unit impulse in input channel $j$ at time $0$ is the $j$-th column of $C A^{i-1} B$ at time $i$. For the continuous-time system $\dot x = A x + B u$, $y = C x$, the impulse response is $C e^{tA} B$ instead, and the Markov parameters are its derivatives at $t = 0$, $C A^{i-1} B = \frac{d^{i-1}}{dt^{i-1}} C e^{tA} B \big|_{t=0}$; its Taylor coefficients are $C A^{i-1} B / (i-1)!$, since $C e^{tA} B = \sum_{i \ge 1} \frac{t^{i-1}}{(i-1)!}\, C A^{i-1} B$.

Sontag's proof: the reductions of [reachable and unobservable subspaces](reachable-and-unobservable-reductions.md) turn any realization into a canonical one of no larger dimension with the same Markov parameters, which proves part 1 and shows that a minimal realization is canonical. Conversely, by [the Hankel factorization](hankel-factorization-of-markov-parameters.md) a canonical realization of dimension $n$ has $\operatorname{rank} H_{n,n}(\mathcal{A}) = n$ ($H_{0,0}$ is the empty matrix, of rank $0$), while every realization of dimension $k$ forces $\operatorname{rank} H_{n,n}(\mathcal{A}) \le k$.

## Depends on

- [Hankel factorization of Markov parameters](hankel-factorization-of-markov-parameters.md): Markov sequences and realizations.
- [Reachability and null-controllability of discrete-time linear systems](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md): the reachability matrix in the definition of a canonical triple.
- [Observability of discrete-time linear systems over a finite horizon](../observability-of-linear-systems/observability-rank-condition-discrete-time.md): the observability matrix in the definition of a canonical triple.

## Proof depends on

- [Reachable and unobservable subspaces and the reduced systems](reachable-and-unobservable-reductions.md): reduction to a canonical triple with the same Markov parameters.
- [Hankel factorization of Markov parameters](hankel-factorization-of-markov-parameters.md): the rank bounds for Hankel matrices.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 6.5: Definition 6.5.3, Corollary 6.5.4, Definition 6.5.9 and Theorem 27, parts 1 and 2, with its proof (pp. 284–287).
