# Parameter regions for multistationarity via positive parameterizations

**Positive parameterization.** For a reaction network $\dot x = N v(x)$ with rank $s$ and conservation
matrix $W \in \mathbb{R}^{d \times n}$ (as in the determinant criterion), a positive parameterization of
the positive equilibria is a surjective map

$$\Phi : \mathbb{R}^m_{>0} \to \{ f = 0 \} \cap \mathbb{R}^n_{>0}, \qquad \hat x \mapsto \Phi(\hat x),$$

with $m < n$ (typically $m = d$). The equilibrium $\Phi(\hat x)$ lies in the class $P_c$ with
$c = W \Phi(\hat x)$. Define

$$a(\hat x) = \det M\bigl(\Phi(\hat x)\bigr), \qquad \hat x \in \mathbb{R}^m_{>0},$$

where $M$ is the Jacobian of the conservation-augmented system $\varphi_c$. For mass-action kinetics
with an algebraic parameterization, $a$ is a rational function of $\hat x$ and of the rate constants.

**Corollary.** Assume (i) the network is dissipative, (ii) no class with nonempty interior contains
boundary equilibria, and (iii) a positive parameterization exists. Then:

1. if $\operatorname{sign} a(\hat x) = (-1)^s$ for all $\hat x \in \mathbb{R}^m_{>0}$, every class
   with $P_c^+ \neq \emptyset$ contains exactly one positive equilibrium, and it is non-degenerate;
2. if $\operatorname{sign} a(\hat x) = (-1)^{s+1}$ for some $\hat x$, then the class with
   $c = W\Phi(\hat x)$ contains at least two positive equilibria, at least one non-degenerate (at
   least three, an odd number, if all are non-degenerate).

**Checking the hypotheses.**

- *Dissipativity.* If for each $c$ there are $\omega_c \in \mathbb{R}^n_{>0}$ and $R > 0$ with
  $\omega_c \cdot f(x) < 0$ for all $x \in P_c$ with $\lVert x \rVert > R$, the network is dissipative;
  conservative networks (with a positive conservation law) are dissipative.
- *No boundary equilibria (siphon criterion).* A siphon is a set $Z$ of species such that every
  reaction producing a species of $Z$ consumes some species of $Z$. If every minimal siphon contains
  the support of a conservation relation with positive coefficients, no class with nonempty interior
  has boundary equilibria.

## Depends on

- [Determinant criterion for unique and multiple equilibria in reaction networks](determinant-criterion-for-unique-and-multiple-equilibria.md)

## Expansion

The parameterization removes the need to locate equilibria: every positive equilibrium is
$\Phi(\hat x)$ for some free variables $\hat x$, so the sign condition of the determinant criterion
becomes a sign condition on the single function $a$ over the positive orthant, and the conservation
totals that realize multistationarity are read off as $c = W \Phi(\hat x)$. For mass-action systems,
$a(\hat x)$ is a polynomial (after clearing a positive denominator) in $\hat x$ whose coefficients
are polynomials in the rate constants $\kappa$. If every coefficient has sign $(-1)^s$, the network is
monostationary for all rate constants; if some coefficient can take sign $(-1)^{s+1}$, choosing
$\hat x$ to make the corresponding monomial dominant (for example a vertex of the Newton polytope)
yields an explicit region of rate constants admitting multistationarity. In a hybrid histidine
kinase model with six species and rank four, $a$ contains the single term
$\kappa_2\kappa_4\kappa_5^2(\kappa_1 - \kappa_3)\, x_4 x_5^2$ of indefinite sign: for
$\kappa_1 \ge \kappa_3$ every term of $\det M$ is positive and the equilibrium is unique in every class,
while for $\kappa_1 < \kappa_3$ the monomial $x_4 x_5^2$ is a vertex of the Newton polytope of $a$, so
some class contains multiple positive equilibria.

## Sources

- C. Conradi, E. Feliu, M. Mincheva, C. Wiuf, "Identifying parameter regions for
  multistationarity", PLoS Computational Biology 13 (2017) e1005751, Eqs. (7)-(10), Corollary 2,
  Propositions 1-2 and the hybrid histidine kinase example,
  <https://doi.org/10.1371/journal.pcbi.1005751> (PMC5626113).
