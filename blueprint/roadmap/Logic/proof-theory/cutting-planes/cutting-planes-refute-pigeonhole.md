# Polynomial-size cutting planes refutations of the pigeonhole principle

For $m > n$, the inequality translation of $\mathrm{PHP}^m_n$ has a cutting planes refutation with $O(n m^2)$ lines, in particular $O(n^3)$ lines for $\mathrm{PHP}^{n+1}_n$. The refutation derives the hole inequalities $\sum_i x_{ij} \le 1$ for each hole by induction on the number of pigeons using rounded division, sums them to $\sum_{i,j} x_{ij} \le n$, and adds the pigeon inequalities $\sum_j x_{ij} \ge 1$ to obtain $0 \ge m - n$, which rounded division by $m - n$ turns into $0 \ge 1$.

## Proof sketch

The case $t = 1$ is a hole clause. For $t \ge 2$, to derive $\sum_{i \le t+1} x_{ij} \le 1$, multiply $\sum_{i \le t} x_{ij} \le 1$ by $t-1$ and add the $t$ pairwise inequalities $x_{ij} + x_{t+1,j} \le 1$ ($i \le t$), giving $t\sum_{i \le t+1} x_{ij} \le 2t - 1$; divide by $t$ and round down. Each hole costs $O(m^2)$ lines.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)

## Sources

- W. Cook, C. R. Coullard and Gy. Turán, "On the Complexity of Cutting-Plane Proofs", Discrete Applied Mathematics 18(1), 25–38, 1987.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.7.2.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
