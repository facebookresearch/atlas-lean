# Spectral sensitivity lower-bounds quantum queries, and D(f) = O(Q(f)⁶)

Every $T$-query algorithm computing a total Boolean function $f$ with error $\varepsilon \le 1/2$ satisfies $\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\lambda(f) \le 2T$. Combined with $\deg(f) \le \lambda(f)^2$ this gives $\deg(f) \le 1296\, Q_{1/3}(f)^2$; with $D(f) \le \deg(f)^2\, bs(f)$ and $bs(f) = O(Q(f)^2)$,

$$D(f) = O\big(Q_{1/3}(f)^6\big).$$

## Proof sketch

Spectral sensitivity is a spectral adversary bound with $\Gamma$ the adjacency matrix of the sensitivity graph, for which $\|\Gamma \circ D_i\| \le 1$. The polynomial method gives $bs(f) \le 6\widetilde{\deg}(f)^2 \le O(Q(f)^2)$.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)
- [Sensitivity graph and spectral sensitivity](../../../TheoryOfComputation/communication-complexity/sensitivity-certificates-and-degree/spectral-sensitivity.md)
- [Decision-tree depth and degree of a Boolean function](../../../TheoryOfComputation/communication-complexity/query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Spectral and negative-weight adversaries and their hierarchy](../quantum-adversary-methods/spectral-and-negative-weight-adversary-hierarchy.md)
- [Degree is at most the square of spectral sensitivity](../../../TheoryOfComputation/communication-complexity/sensitivity-certificates-and-degree/degree-at-most-spectral-sensitivity-squared.md)
- [Polynomial method for quantum query complexity](../quantum-query-lower-bounds/polynomial-method-for-quantum-query-complexity.md)
- [Nisan–Szegedy: block sensitivity is at most quadratic in degree and approximate degree](../../../TheoryOfComputation/communication-complexity/sensitivity-certificates-and-degree/nisan-szegedy-bounds.md)
- [Certificate complexity, degree and decision-tree depth](../../../TheoryOfComputation/communication-complexity/query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- S. Aaronson, S. Ben-David, R. Kothari, S. Rao and A. Tal, "Degree vs. Approximate Degree and Quantum Implications of Huang's Sensitivity Theorem", STOC 2021.
- H. Huang, "Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture", Annals of Mathematics 190(3), 2019.
