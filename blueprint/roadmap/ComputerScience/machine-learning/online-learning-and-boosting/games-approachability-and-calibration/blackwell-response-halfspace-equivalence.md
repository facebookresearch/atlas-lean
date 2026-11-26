# Blackwell's characterization: response condition iff every containing halfspace is forceable

Let $I, J$ be finite nonempty sets, $E$ a real inner product space, $m : I \times J \to E$ a vector payoff and $S \subseteq E$ a nonempty complete convex set. Write $m(p,q) = \sum_{i,j} p(i)q(j)\,m(i,j)$. The following are equivalent.

1. (Response condition.) For every $q \in \Delta(J)$ there is $p \in \Delta(I)$ with $m(p,q) \in S$.
2. (Halfspace condition.) For every closed halfspace $\{x : \langle w, x\rangle \le c\} \supseteq S$ there is $p \in \Delta(I)$ with $\langle w, \sum_i p(i)\,m(i,j)\rangle \le c$ for every $j \in J$.

No finite-dimensionality of $E$ is assumed.

## Proof sketch

(1) implies (2) by von Neumann's minimax theorem applied to the scalar game $\langle w, m(i,j)\rangle$: every column mixture has a row response with value at most $c$, hence a single row mixture works against all columns. For (2) implies (1), if some $q$ has no response, the compact convex set $\{m(p,q) : p\}$ is disjoint from $S$; the nearest pair gives a separating hyperplane $w$ from the metric projection, and the corresponding halfspace contains $S$ but cannot be forced against $q$.

## Depends on

- [Blackwell's approachability theorem](../../../../GameTheory/noncooperative-games/blackwell-approachability/blackwell-approachability.md)
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Proof depends on

- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)
- [Blackwell's half-space step](../../../../GameTheory/noncooperative-games/blackwell-approachability/exists-inner-sub-nonpos-of-enforceable.md)

## Sources

- David Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific Journal of Mathematics, 1956.
