# Polynomial-size cutting planes refutations of the pigeonhole principle

For $m > n$, the inequality translation of $\mathrm{PHP}^m_n$ has a cutting planes refutation of polynomial size; for $\mathrm{PHP}^{n+1}_n$ one with at most $(n+1)(n+2)^2$ lines. The refutation derives the hole inequalities $\sum_i x_{ij} \le 1$ for each hole by induction on the number of pigeons using rounded division, sums them to $\sum_{i,j} x_{ij} \le n$, and adds the pigeon inequalities $\sum_j x_{ij} \ge 1$ to obtain $0 \ge m - n \ge 1$.

## Proof sketch

To derive $\sum_{i \le t+1} x_{ij} \le 1$ from $\sum_{i \le t} x_{ij} \le 1$ and the pairwise inequalities $x_{ij} + x_{t+1,j} \le 1$, add all of them to get twice the target plus slack, then divide by two and round.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)

## Proof depends on

- [Soundness and refutation completeness of cutting planes](cutting-planes-soundness-and-completeness.md)

## Sources

- W. Cook, C. R. Coullard and Gy. Turán, "On the Complexity of Cutting-Plane Proofs", Discrete Applied Mathematics 18(1), 25–38, 1987.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
