# Jacobian factorization threshold and next-generation reproduction numbers

**Setting.** Consider a compartmental epidemic ODE with a disease-free equilibrium (DFE) and a chosen set of disease ("zeroable") compartments, satisfying the hypotheses (A1)–(A5) of van den Driessche and Watmough; in particular the Jacobian of the non-disease compartments at the DFE has all eigenvalues with negative real part. Write the disease equations as $\dot{\mathbf i} = \mathcal F - \mathcal V$ and let $F$, $V$ be the gradients of $\mathcal F$ and $\mathcal V$ at the DFE. The decomposition is **admissible** if $F$ has no negative terms in its expanded symbolic form and $V$ is a nonsingular M-matrix ($-V$ a sub-generator matrix) for nonnegative parameters. Its reproduction number is the [basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/r0.md) $R_F = \rho(FV^{-1})$ of the next-generation matrix. Every admissible $R_F$ has the threshold property: the Jacobian at the DFE has an eigenvalue with positive real part if and only if $R_F > 1$. Different admissible decompositions can give different values of $R_F$.

**Jacobian factorization threshold.** A polynomial with real parametric coefficients is of **Descartes type** if all coefficients except the constant one are sign-definite and of the same sign; by Descartes' rule of signs, such a polynomial with positive leading coefficient has a positive root iff its constant term $c_0$ is negative. Factor the characteristic polynomial of the Jacobian at the DFE over the rationals, normalise the factors to positive leading coefficient, discard linear factors with parameter-independent negative roots, and for each remaining factor of Descartes type write its constant term as $c_0^{(i)} = c_+^{(i)} - c_-^{(i)}$ (positive and negative parts of its expansion). Define

$$R_J^{(i)} = \frac{c_-^{(i)}}{c_+^{(i)}}, \qquad R_J = \max_i R_J^{(i)}.$$

**Theorem.**

1. $R_J^{(i)} > 1$ iff $c_0^{(i)} < 0$. Hence, if $R_J > 1$, the Jacobian at the DFE has a positive real eigenvalue and the DFE is unstable.
2. If $R_J > 1$, then $R_F > 1$ for every admissible decomposition. Equivalently, $R_J \le 1$ whenever $R_F \le 1$ for some admissible decomposition.

The converse of item 1 can fail, since $R_J$ reads only the factors of Descartes type, and no inequality between the values of $R_J$ and $R_F$ holds in general on either side of the threshold. For SEIR with disease compartments $(E, I)$, $\dot E = \beta S I - (\sigma+\mu)E$ and $\dot I = \sigma E - (\gamma+\mu)I$, at the DFE $S_0$, the disease factor $\lambda^2 + (\sigma+\gamma+2\mu)\lambda + (\sigma+\mu)(\gamma+\mu) - \sigma\beta S_0$ is of Descartes type and gives $R_J = \sigma\beta S_0/((\sigma+\mu)(\gamma+\mu))$. The usual decomposition gives $R_F = R_J$, while the admissible decomposition $\mathcal F = (\beta S I, \sigma E)$, $\mathcal V = ((\sigma+\mu)E, (\gamma+\mu)I)$ gives $R_{F'} = \sqrt{R_J}$, which is smaller than $R_J$ when $R_J > 1$ and larger when $R_J < 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Proof sketch

Item 1: $c_\pm^{(i)} > 0$, so $R_J^{(i)} > 1$ iff $c_0^{(i)} < 0$, and a Descartes factor with negative constant term has a positive root. Item 2: by (A5) a positive real eigenvalue $\lambda$ of the Jacobian at the DFE is an eigenvalue of the disease block $F - V$, which is the same matrix for every admissible decomposition. So $F - V$ has an eigenvalue with positive real part, and $R_F > 1$ by the threshold property of $\rho(FV^{-1})$.

## Sources

- Florin Avram, Rim Adenane, Lasko Basnarkov and Matthew D. Johnston, "Algorithmic Approach for a Unique Definition of the Next-Generation Matrix", *Mathematics* 12 (2023), 27, <https://doi.org/10.3390/math12010027>. Preprint version: arXiv:2311.16686 (2023), the definitions of admissible $(F,V)$ decompositions and Descartes multi-strain models, the DFE stability proposition, and the section on the Jacobian factorization threshold, <https://doi.org/10.48550/arXiv.2311.16686>.
