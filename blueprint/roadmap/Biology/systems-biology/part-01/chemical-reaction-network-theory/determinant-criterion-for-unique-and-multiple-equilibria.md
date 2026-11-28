# Global determinant criterion for a unique positive equilibrium in every class

**Setting.** As in the [uniqueness criterion](../../../not-yet-classified/multistationarity-degree-criterion/exists-unique-equilibrium.md) and the
[multistationarity criterion](../../../not-yet-classified/multistationarity-degree-criterion/multiple-equilibria.md) (Conradi, Feliu, Mincheva and Wiuf 2017,
Theorem 1 (A′) and (B′)): an [admissible](../../../not-yet-classified/multistationarity-degree-criterion/admissible.md) [reaction system](../../../not-yet-classified/multistationarity-degree-criterion/reaction-system.md)
$\dot x = f(x) = N v(x)$ with stoichiometric matrix $N$ of rank $s$, a
[row-reduced conservation matrix](../../../not-yet-classified/multistationarity-degree-criterion/is-row-reduced-conservation.md) $W$ with pivots, the classes
$P_c = \{x \ge 0 : W x = c\}$ and $P_c^+ = P_c \cap \mathbb{R}^n_{>0}$, and the matrix
[$M(x)$](../../../not-yet-classified/multistationarity-degree-criterion/m.md), the Jacobian of the system $\varphi_c$ obtained from $f$ by replacing its pivot
rows with the conservation laws $W x - c$ (it does not depend on $c$). For a class with
$P_c^+ \ne \emptyset$, when the semiflow is dissipative and $P_c$ has no boundary equilibria, those
criteria give exactly one positive equilibrium in $P_c$, nondegenerate, if
$\operatorname{sign}\det M(x) = (-1)^s$ at every positive equilibrium $x \in P_c^+$, and at least
two if $\operatorname{sign}\det M(x) = (-1)^{s+1}$ at some positive equilibrium in $P_c^+$.

**Corollary.** Assume the semiflow is [dissipative](../../../not-yet-classified/multistationarity-degree-criterion/dissipative.md) and no class $P_c$ with
$P_c^+ \ne \emptyset$ contains boundary equilibria. If $\operatorname{sign}\det M(x) = (-1)^s$ for
all $x \in \mathbb{R}^n_{>0}$ (for instance, for injective networks), then every class with
$P_c^+ \ne \emptyset$ contains exactly one positive equilibrium, and it is
[nondegenerate](../../../not-yet-classified/multistationarity-degree-criterion/nondegenerate.md).

## Depends on

- [Uniqueness criterion](../../../not-yet-classified/multistationarity-degree-criterion/exists-unique-equilibrium.md)
- [Multistationarity criterion](../../../not-yet-classified/multistationarity-degree-criterion/multiple-equilibria.md)
- [M](../../../not-yet-classified/multistationarity-degree-criterion/m.md)
- [Dissipative](../../../not-yet-classified/multistationarity-degree-criterion/dissipative.md)
- [Nondegenerate](../../../not-yet-classified/multistationarity-degree-criterion/nondegenerate.md)

## Expansion

The hypothesis on $\det M$ holds at every positive point, so in particular at every positive
equilibrium of every class; applying the uniqueness criterion to each class with
$P_c^+ \ne \emptyset$ gives the conclusion. Both criteria come from the Brouwer degree of
$\varphi_c$ on a bounded neighbourhood of the compact absorbing set inside $P_c$: dissipativity and
the absence of boundary equilibria force the degree to be $(-1)^s$, and the degree is the sum of
$\operatorname{sign}\det M(x^*)$ over the nondegenerate zeros. A sign that holds on all of
$\mathbb{R}^n_{>0}$ needs no knowledge of where the equilibria are, which is what makes the
corollary checkable from the rate functions alone; injective networks are the classical case.

## Sources

- C. Conradi, E. Feliu, M. Mincheva, C. Wiuf, "Identifying parameter regions for
  multistationarity", PLoS Computational Biology 13 (2017) e1005751, Eqs. (2)-(6), Theorem 1 and
  Corollary 1, <https://doi.org/10.1371/journal.pcbi.1005751> (PMC5626113).
