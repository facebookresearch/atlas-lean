# Linearization of IPS refutations

Every IPS refutation can be turned into a linear (Hilbert-like) IPS refutation of polynomially related size: for formulas when the field has more than $d$ elements, $d$ bounding the degrees, and for circuits with no condition on the field, because the axioms are themselves computed by small formulas or circuits.

**Theorem.** Let $\mathbb{F}$ be a field and let $f_1, \dots, f_m \in \mathbb{F}[x_1, \dots, x_n]$ have an IPS refutation $C \in \mathbb{F}[\vec{x}, y_1, \dots, y_m]$. Then $f_1, \dots, f_m$ have a linear IPS refutation $C'(\vec{x}, \vec{y}) = \sum_{j=1}^{m} g_j(\vec{x}) \, y_j$, that is, $\sum_j g_j f_j = 1$, in each of the following cases.

1. If $f_1, \dots, f_m$ and $C$ are computed by algebraic formulas of size $s$ and have degree at most $d$, and $|\mathbb{F}| \ge d + 1$, then $C'$ is computed by an algebraic formula of size $\mathrm{poly}(s, d, m)$.
2. If $f_1, \dots, f_m$ and $C$ are computed by algebraic circuits of size $s$, then $C'$ is computed by an algebraic circuit of size $\mathrm{poly}(s, m)$.

In both cases $C'$ can be constructed in time polynomial in its size bound from $d$ and the given formulas or circuits.

## Proof sketch

Write $C = \sum_{\vec{a} > \vec{0}} C_{\vec{a}}(\vec{x}) \vec{y}^{\vec{a}}$, using $C(\vec{x}, \vec{0}) = 0$, and group the exponents $\vec{a}$ by the index $i$ of their first nonzero entry; each group is $y_i$ times a polynomial $D_i(\vec{x}, y_i, \dots, y_m)$. Then $C' = \sum_i D_i(\vec{x}, f_i, \dots, f_m) \, y_i$ satisfies $C'(\vec{x}, \vec{f}) = C(\vec{x}, \vec{f}) = 1$. The quotients $D_i$ are computed from $C$ by dividing by a variable: by interpolation over $d + 1$ field points for formulas, and by a gate-by-gate construction for circuits. Substituting the small formulas or circuits for the $f_j$ keeps the size polynomial, even for circuits of unbounded degree.

## Depends on

- [Ideal Proof System](ideal-proof-system.md)
- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)
- [Polynomial-time computable functions](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

None.

## Sources

- Michael A. Forbes, Amir Shpilka, Iddo Tzameret, Avi Wigderson, "Proof complexity lower bounds from algebraic circuit complexity", *31st Computational Complexity Conference (CCC 2016)*, LIPIcs 50, 2016, https://doi.org/10.4230/LIPIcs.CCC.2016.32; numbering of arXiv:1606.05050v1 (Proposition 4.4, Lemmas 4.1 and 4.2).
