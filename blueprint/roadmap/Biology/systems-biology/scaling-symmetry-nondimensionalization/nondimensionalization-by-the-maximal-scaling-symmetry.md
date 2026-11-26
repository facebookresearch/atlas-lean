# Nondimensionalization by the maximal scaling symmetry

**Setting.** A rational first-order ODE system $\dot z = F(z; k)$ in time $t$, state $z \in \mathbb R^q$ and parameters $k \in \mathbb R^p$ admits a *scaling symmetry* given by an integer matrix $\bar A = [A_0\ A] \in M_{r \times (n+1)}(\mathbb Z)$: for every $\lambda \in (\mathbb R^*)^r$ the substitution $t \mapsto \lambda^{A_t} t$, $z_j \mapsto \lambda^{A_{z_j}} z_j$, $k_i \mapsto \lambda^{A_{k_i}} k_i$ maps solutions to solutions. Choose the *maximal* such symmetry (of rank $r$). A *Hermite multiplier* of $A$ is a unimodular $V$ with $AV$ in column Hermite normal form; let $W = V^{-1} = \bigl[\begin{smallmatrix} W_{\mathfrak a} \\ W_{\mathfrak b}\end{smallmatrix}\bigr]$.

**Theorem.**
1. The normal Hermite multiplier exists and is unique, and the last $n - r$ columns of any Hermite multiplier form a basis of $\ker A$; the corresponding monomials in $(t, z, k)$ generate the field of rational invariants of the scaling action.
2. *(Reduction.)* The system can be rewritten exactly in one dimensionless time $\tau$, $q$ dimensionless dependent variables $\nu$ and $p - r$ dimensionless parameters $\kappa$, by substituting $t \mapsto \kappa^{W_t}\tau$, $z \mapsto \kappa^{W_z}\nu$ with exponents read from $W$.
3. *(Prescribed combinations.)* The reduced system can be written in terms of parameter monomials with exponent matrix $P$ if and only if $AP = 0$ and $W_{\mathfrak b} P$ extends to a unimodular integer matrix.
4. *(Invariance.)* If two ODE systems are related by an invertible change of variables, the rank of the maximal scaling symmetry that also keeps the change of variables dimensionally consistent is the same for both systems. Hence the number of dimensionless parameters does not depend on how the model is written.

## Expansion

Physical dimensions are one particular scaling symmetry; the maximal symmetry contains them and possibly more, so it gives the largest reduction compatible with the rational structure. Integer linear algebra (Hermite and Smith normal forms) replaces the ad hoc choice of reference scales: unimodularity guarantees that the substitution is invertible over rational monomials, so no information is lost. Applied to Michaelis–Menten kinetics the method recovers the classical dimensionless forms and decides which proposed parameter groupings are admissible.

## Sources

- R. Tanburn, D. Hendron, P. Maini, S. Amethyst, "Nondimensionalization is more science than art", arXiv:2512.13455 (2025), Theorems 1, 2, 3, 4 and 6, <https://doi.org/10.48550/arXiv.2512.13455>.
