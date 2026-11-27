# Spectral sensitivity lower-bounds quantum queries, and D(f) = O(Q(f)⁶)

For every Boolean function $f$, the spectral sensitivity is at most the bounded-error quantum query complexity up to a constant factor, $\lambda(f) = O(Q(f))$; hence, by $\deg(f) \le \lambda(f)^2$, every total Boolean function satisfies $\deg(f) = O(Q(f)^2)$. For every total Boolean function

$$D(f) = O\big(Q(f)^6\big).$$

## Proof sketch

Spectral sensitivity is a spectral adversary bound: taking $\Gamma$ to be the adjacency matrix of the sensitivity graph gives $\|\Gamma\| = \lambda(f)$ and $\|\Gamma \circ D_i\| \le 1$, so $\lambda(f) \le \mathrm{SA}(f) = O(Q(f))$ by Barnum–Saks–Szegedy. The sixth-power relation between $D(f)$ and $Q(f)$ for total functions is the classical consequence of Nisan, Nisan–Szegedy and Beals et al. (polynomial method). (Derived, not stated in this form by the sources: the spectral adversary bound has constant $(1 - 2\sqrt{\varepsilon(1-\varepsilon)})/2$, so every $T$-query algorithm with error $\varepsilon \le 1/2$ satisfies $\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\lambda(f) \le 2T$; with $1 - 2\sqrt{2}/3 \ge 1/18$ this gives $\deg(f) \le 1296\, Q(f)^2$, and with $D(f) \le \deg(f)^2\, bs(f)$ and $bs(f) \le 6\widetilde{\deg}(f)^2 \le 24\, Q(f)^2$ it gives the sixth-power bound again. Aaronson et al. obtain the stronger $D(f) = O(Q(f)^4)$ by combining $\deg(f) = O(Q(f)^2)$ with an unrefereed result of Midrijanis.)

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

- S. Aaronson, S. Ben-David, R. Kothari, S. Rao and A. Tal, "Degree vs. Approximate Degree and Quantum Implications of Huang's Sensitivity Theorem", Proceedings of the 53rd ACM Symposium on Theory of Computing (STOC 2021); arXiv:2010.12629: Equation (2) (the known relation $D(f) = O(Q(f)^6)$ for total functions), Theorem 3 and Lemma 9.
- H. Huang, "Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture", Annals of Mathematics 190(3), 2019.
- H. Barnum, M. Saks and M. Szegedy, "Quantum Query Complexity and Semi-Definite Programming", 18th IEEE Conference on Computational Complexity (CCC 2003), 2003.
