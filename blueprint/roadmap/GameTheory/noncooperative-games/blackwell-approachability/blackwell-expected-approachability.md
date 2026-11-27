# Blackwell's approachability theorem, expected-payoff form

Let $v : A \times B \to E$ be a vector payoff into a real Hilbert space, with $A$ finite and
$\|v(a, b)\| \le R$, and let $C \subseteq E$ be nonempty, closed and convex. If every closed
half-space containing $C$ is enforceable, there is a strategy $\sigma$ (a map from the current average
expected payoff to a mixed action) such that, against every sequence $\beta$ of opponent actions and
for every $c_0 \in C$,

$$\operatorname{dist}(\bar x_n, C) \le \frac{3R + \|c_0\|}{\sqrt n} \qquad (n \ge 1),$$

where $\bar x_n$ is the average of the first $n$ expected payoffs. The constant $3R + \|c_0\|$ bounds $\|y_n - c_n\|$ and plays the role of Hart's $M$ in
the recursion (13); it is not Hart's constant. Since the mixed actions are
determined by the opponent's sequence, this covers opponents who adapt to the past.

Blackwell's half-space construction provides such a $\sigma$. This is the expected-payoff estimate in
the proof of Blackwell's theorem; the almost-sure
convergence of the realised payoffs additionally needs a strong law of large numbers for
martingale differences; see [Blackwell's approachability theorem](blackwell-approachability.md).

## Informally uses

- [Blackwell's half-space step](exists-inner-sub-nonpos-of-enforceable.md): the choice of the
  mixed action at each stage.
- [The M/√t rate of approachability](inf-dist-average-le.md): the resulting rate.

## Background

- [Von Neumann's minimax theorem](../von-neumann-s-minimax-theorem/README.md): a half-space
  $\{\lambda\cdot x \le \rho\}$ is enforceable exactly when the minimax value of the scalar game
  $\lambda \cdot v$ is at most $\rho$ (Hart 2005, Appendix).

## Sources

- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, Appendix, Theorem 5 and its proof.
- D. Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific J. Math. 6 (1956), 1–8, Theorem 1.
