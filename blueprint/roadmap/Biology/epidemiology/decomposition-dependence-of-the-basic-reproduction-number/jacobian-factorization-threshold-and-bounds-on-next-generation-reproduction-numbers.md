# Jacobian factorization threshold and bounds on next-generation reproduction numbers

**Setting.** For a compartmental epidemic ODE with a disease-free equilibrium (DFE) and a chosen set of disease ("zeroable") compartments, write the disease equations as $\dot{\mathbf i} = \mathcal F - \mathcal V$ and let $F$, $V$ be the gradients of $\mathcal F$ and $\mathcal V$ at the DFE. The decomposition is **admissible** if $F$ has no negative terms in its expanded symbolic form and $-V$ is a sub-generator matrix (for nonnegative parameters). For every admissible decomposition, $R_F = \rho(FV^{-1})$, the Perron–Frobenius eigenvalue of the next-generation matrix, satisfies the threshold property: the DFE is unstable if $R_F > 1$ and locally stable if $R_F < 1$. Different admissible decompositions give different $R_F$, all sharing the threshold $1$.

**Jacobian factorization threshold.** A polynomial with real parametric coefficients is of **Descartes type** if all coefficients except the constant one are sign-definite and of the same sign; by Descartes' rule of signs, such a polynomial with positive leading coefficient has a positive root iff its constant term $c_0$ is negative. Factor the characteristic polynomial of the Jacobian at the DFE over the rationals, normalise the factors to positive leading coefficient, discard linear factors with parameter-independent negative roots, and for each remaining factor of Descartes type write its constant term as $c_0^{(i)} = c_+^{(i)} - c_-^{(i)}$ (positive and negative parts of its expansion). Define

$$R_J^{(i)} = \frac{c_-^{(i)}}{c_+^{(i)}}, \qquad R_J = \max_i R_J^{(i)}.$$

Then $c_0^{(i)} < 0 \iff R_J^{(i)} > 1$, so $R_J > 1$ iff the DFE is unstable; for a Descartes multi-strain model (whose characteristic polynomial factors into $M$ Descartes polynomials) the local stability set is contained in $\{R_J \le 1\}$.

**Theorem.** For a model whose DFE Jacobian factors as above:
1. on the instability domain, $R_J \le \inf_{F\ \text{admissible}} R_F$;
2. on the stability domain, $R_J \ge \sup_{F\ \text{admissible}} R_F$.

So $R_J$ sits between all admissible next-generation reproduction numbers on each side of the threshold. The paper also proposes an algorithmic, expert-free choice of $(F,V)$: take $F$ as the positive part of all disease-equation terms involving both disease and susceptible (input) compartments, after removing output compartments that are determined by the others.

## Expansion

If $R_J > 1$ then some Descartes factor has a positive root, so the DFE is unstable, which by the threshold property forces $R_F > 1$ for every admissible $F$; since this holds for every parameter value, the region $\{R_J > 1\}$ is inside $\{R_F > 1\}$, which yields the ordering of part 1, and part 2 is symmetric. The point is that $R_0$ is not a function of the ODE alone but of the ODE plus a decomposition; the Jacobian factorization threshold is decomposition-free but in general is not a spectral radius, and the two agree for many simple multi-strain models.

## Sources

- Florin Avram, Rim Adenane, Lasko Basnarkov and Matthew Johnston, "Algorithmic approach for an unique definition of the next generation matrix", arXiv:2311.16686 (2023), the definitions of admissible $(F,V)$ decompositions and Descartes multi-strain models, the DFE stability proposition and the theorem of the section on the Jacobian factorization bound, <https://doi.org/10.48550/arXiv.2311.16686>.
