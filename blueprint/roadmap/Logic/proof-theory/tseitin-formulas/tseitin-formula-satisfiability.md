# Tseitin formulas are unsatisfiable exactly when the total charge is odd

Let $G$ be a connected multigraph with charge $\chi$. Then $T(G, \chi)$ is satisfiable if and only if $\sum_{v \in V} \chi(v)$ is even. In general $T(G,\chi)$ is satisfiable iff every connected component has even total charge, and when satisfiable its solutions form a coset of the cycle space of $G$ over $\mathbb{F}_2$.

## Proof sketch

Summing all vertex equations counts every edge twice, so a solution forces $\sum_v \chi(v) = 0$ in $\mathbb{F}_2$. Conversely, with even charge pair up charged vertices along paths in a spanning tree and flip the edges of these paths, starting from the all-zero assignment.

## Depends on

- [Tseitin formulas of a multigraph](tseitin-formulas-of-a-multigraph.md)

## Sources

- G. S. Tseitin, "On the Complexity of Derivation in Propositional Calculus", in Automation of Reasoning 2, Springer, 1983 (original 1968).
- A. Urquhart, "Hard Examples for Resolution", Journal of the ACM 34(1), 209–219, 1987.
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Definition 4.1.
