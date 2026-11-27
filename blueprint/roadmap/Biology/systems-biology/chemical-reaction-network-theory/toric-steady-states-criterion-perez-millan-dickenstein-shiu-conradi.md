# Criterion for toric steady states

For a mass action system with $s$ species, $m$ complexes $y_1, \dots, y_m \in \mathbb{Z}^s_{\ge 0}$ and complex-to-species rate matrix $\Sigma$, Pérez Millán, Dickenstein, Shiu and Conradi (2012) say that the system has toric steady states if its steady-state ideal is a binomial ideal admitting real zeros. Condition 3.1 asks for a partition $I_1, \dots, I_d$ of the complexes and a basis $b_1, \dots, b_d$ of $\ker\Sigma$ with $\operatorname{supp}(b_j) = I_j$; it makes the steady-state ideal binomial. Condition 3.4 asks that the two coefficients of each resulting binomial have the same sign, and Condition 3.6 asks that the associated linear system for $\ln x$ be solvable. Theorem 3.8 states: a system satisfying Condition 3.1 admits a positive toric steady state if and only if Conditions 3.4 and 3.6 hold. Under all three conditions, let $A \in \mathbb{Z}^{w \times s}$ be a matrix of maximal rank $w$ whose kernel is the span of all differences $y_{j_2} - y_{j_1}$ with $j_1, j_2$ in a common block $I_j$, and let $A_1, \dots, A_s$ be its columns; Theorem 3.11 shows that every positive steady state has the form $x = (\tilde x_1 t^{A_1}, \dots, \tilde x_s t^{A_s})$ for a fixed positive steady state $\tilde x$ and some $t \in \mathbb{R}^w_{>0}$, so the positive steady-state locus has dimension $w$ and a monomial parametrization; and Theorem 4.3 shows that the $n$-site phosphorylation system has toric steady states with a three-dimensional steady-state locus.

## Depends on

- [Mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

1. The model: mass action systems, the matrix $\Sigma$, the steady-state ideal and toric steady states.
2. Conditions 3.1, 3.4 and 3.6 with their linear-algebra data, and Lemma 3.5 for checking Condition 3.4.
3. The criterion (Theorem 3.8) and the monomial parametrization (Theorem 3.11).
4. The application to the $n$-site phosphorylation system (Theorem 4.3), with its explicit parametrization; compare [rational parameterisation of multisite modification steady states](multisite-phosphorylation/rational-parameterisation-theorem-for-multisite-ptm-systems.md).

## Sources

- M. Pérez Millán, A. Dickenstein, A. Shiu and C. Conradi, Chemical reaction systems with toric steady states, Bull. Math. Biol. 74 (2012), 1027–1065, Conditions 3.1, 3.4, 3.6 and Theorems 3.8, 3.11, 4.3. <https://arxiv.org/abs/1102.1590>
