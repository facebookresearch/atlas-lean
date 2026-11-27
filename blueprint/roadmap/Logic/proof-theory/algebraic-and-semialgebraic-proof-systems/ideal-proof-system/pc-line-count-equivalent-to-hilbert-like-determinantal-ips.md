# Polynomial calculus line count is p-equivalent to Hilbert-like determinantal IPS

Polynomial calculus with size measured by its number of lines is p-equivalent to Hilbert-like IPS over weakly skew circuits, i.e. determinantal IPS; likewise Pitassi's 1996 algebraic system, whose proofs are circuits for the coefficients of a Nullstellensatz certificate, is p-equivalent to Hilbert-like IPS over general circuits.

Let $\mathbb{F}$ be a field and $F_1, \dots, F_m \in \mathbb{F}[x_1, \dots, x_n]$. A Hilbert-like IPS certificate is one of the form $\sum_{i=1}^{m} y_i \, G_i(\vec{x})$, and $\mathrm{VP}_{ws}$ is the class of polynomial families computed by polynomial-size weakly skew circuits (the class $\mathsf{VBP}$ of the linked page), equivalently by p-projections of the determinant.

**Proposition.**

1. Pitassi's 1996 algebraic proof system, in which a proof of the unsatisfiability of $F_1 = \dots = F_m = 0$ is an algebraic circuit computing a tuple $(G_1, \dots, G_m)$ with $\sum_i G_i F_i = 1$, is p-equivalent to Hilbert-like IPS.
2. Polynomial calculus with size measured by the number of lines (Pitassi's 1997 algebraic proof system) is p-equivalent to Hilbert-like $\mathrm{VP}_{ws}$-IPS, equivalently Hilbert-like determinantal IPS.

## Proof sketch

For part 1, $m$ product gates and one addition gate turn a circuit for $(G_1, \dots, G_m)$ into one for $\sum_i y_i G_i$; conversely, by Baur and Strassen, a circuit for $\sum_i y_i G_i$ yields a circuit of linear size for its partial derivatives $G_i$ with respect to the $y_i$. For part 2, a polynomial calculus derivation is a rule-based circuit in the placeholders: each linear-combination step is an addition gate with scalar weights, and each multiplication by $x_j$ is a product gate with a variable leaf as one input, so the circuit is weakly skew and computes a Hilbert-like certificate. Conversely, a weakly skew circuit computing a Hilbert-like certificate is simulated line by line by polynomial calculus steps.

## Depends on

- [Polynomial calculus](../polynomial-calculus.md)
- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)
- [Valiant's VP versus VNP conjecture](../../../../TheoryOfComputation/algebraic-complexity/valiant-s-vp-versus-vnp-conjecture.md)

## Proof depends on

None.

## Sources

- Joshua A. Grochow, Toniann Pitassi, "Circuit complexity, proof complexity, and polynomial identity testing: the Ideal Proof System", *Journal of the ACM* 65(6), 2018, https://doi.org/10.1145/3230742; numbering of arXiv:1404.3820v1 (Proposition 2.2 and its proof, Section 1.3.3).
