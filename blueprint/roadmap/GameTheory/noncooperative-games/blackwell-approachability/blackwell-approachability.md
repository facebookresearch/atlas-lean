# Blackwell's approachability theorem

Let $v : A \times B \to \mathbb R^d$ be a vector payoff with finite action sets and $C$ a nonempty
closed convex set such that every closed half-space containing $C$ is enforceable. Then $C$ is
approachable: there is a map $\sigma$ from $\mathbb R^d$ to mixed actions on $A$ such that, whatever the
opponent does (possibly randomising and adapting to the past), if from the second round on the
decision maker plays $\sigma$ of the current average payoff, the average realised vector payoff
converges to $C$ almost surely. Blackwell's half-space construction provides such a $\sigma$. The
condition is also necessary (Hart 2005, Theorem 5).

Randomised play is modelled by a process of realised action pairs on a probability space: for every
$n \ge 0$, conditionally on the first $n + 1$ rounds, the decision maker's action in round $n + 2$ has
law $\sigma(\bar x_{n+1})$, where $\bar x_{n+1}$ is the average payoff of those rounds, independently of
the opponent's action in that round. The actions of the first round are unconstrained.

## Informally uses

- [Blackwell's approachability theorem, expected-payoff form](blackwell-expected-approachability.md):
  the expected-payoff recursion, to which a strong law of large numbers for martingale differences
  is added.

## Sources

- D. Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific J. Math. 6 (1956), 1–8, Theorem 1 and §3.
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, Appendix, Theorem 5.
- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §3, Blackwell's Approachability Theorem.
