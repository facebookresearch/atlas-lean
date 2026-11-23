# Blackwell's approachability recursion

Let $C$ be a set in a real inner product space, $\bar x_n$ the averages of a sequence $y$, and
$(c_n)_{n \ge 0}$ points of $C$ such that $c_n$ is a nearest point of $C$ to $\bar x_n$ for $n \ge 1$.
Suppose each new vector lies in the half-space through $c_n$ with outer normal $\bar x_n - c_n$,
$\langle \bar x_n - c_n,\, y_n - c_n\rangle \le 0$ for $n \ge 1$, and $\|y_n - c_n\| \le M$ for every $n$.
Then, with $\delta_n = \operatorname{dist}(\bar x_n, C)^2$,

$$n^2\delta_n \le n M^2 \qquad \text{for every } n.$$

The proof is the recursion $n^2 \delta_n \le (n-1)^2 \delta_{n-1} + M^2$ for $n \ge 1$.

This is the computation in the proof of Blackwell's theorem, here for a deterministic sequence;
in the game it is applied to conditional expectations of the payoffs.

## Informally uses

- [Recursion for the running average](succ-smul-average.md): expanding
  $\|(n+1)(\bar x_{n+1} - c_n)\|^2$.

## Sources

- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, Appendix, proof of Theorem 5 (ii), equation (13).
- D. Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific J. Math. 6 (1956), 1–8, proof of Theorem 1, inequalities (2)–(5).
