# Degree-theory criterion for unique versus multiple equilibria through a positive parametrization

Let a reaction network with stoichiometric matrix $N$ of rank $s$ have rate functions satisfying Eq. (2) of Conradi, Feliu, Mincheva and Wiuf (2017), let $W$ be a matrix in reduced row echelon form whose $d$ rows form a basis of the left kernel of $N$, with pivot (first nonzero) columns $i_1 < \dots < i_d$, and let $\varphi_c$ be the map (Eq. (6) of the source) whose $i$-th component is the species-formation rate of species $i$ for $i \notin \{i_1, \dots, i_d\}$ and, for $i = i_j$, the $j$-th component of $Wx - c$; its Jacobian [$M(x)$](../../not-yet-classified/multistationarity-degree-criterion/m.md) does not depend on $c$. These choices fix the sign of $\det M(x)$: replacing a conservation equation by its negative leaves the zeros of $\varphi_c$ unchanged but reverses the sign of the determinant. Theorem 1 of the source, for one stoichiometric compatibility class, is stated as the [uniqueness criterion](../../not-yet-classified/multistationarity-degree-criterion/exists-unique-equilibrium.md) (A′) and the [multistationarity criterion](../../not-yet-classified/multistationarity-degree-criterion/multiple-equilibria.md) (B′). Corollary 2 of the source restates it when the positive equilibria admit a positive parametrization $\Phi$, with $a(\hat x) = \det M(\Phi(\hat x))$, for a [dissipative](../../not-yet-classified/multistationarity-degree-criterion/dissipative.md) network with no boundary equilibria in any stoichiometric compatibility class with positive points: if $\operatorname{sign} a = (-1)^s$ everywhere there is exactly one positive equilibrium in each class with positive points, and if $\operatorname{sign} a(\hat x) = (-1)^{s+1}$ for some $\hat x$ the class through $\Phi(\hat x)$ is multistationary.

## Depends on

- [M](../../not-yet-classified/multistationarity-degree-criterion/m.md)
- [Dissipative](../../not-yet-classified/multistationarity-degree-criterion/dissipative.md)

## Proof depends on

- [Uniqueness criterion](../../not-yet-classified/multistationarity-degree-criterion/exists-unique-equilibrium.md)
- [Multistationarity criterion](../../not-yet-classified/multistationarity-degree-criterion/multiple-equilibria.md)

## Expansion

1. Positive parametrizations of the equilibrium set, the function $a$ (Eq. (10)) and Corollary 2, derived from Theorem 1 class by class.
2. The procedure of the source for finding parameter regions of mono- and multistationarity, and its applications, as separate statements.

## Sources

- C. Conradi, E. Feliu, M. Mincheva and C. Wiuf, Identifying parameter regions for multistationarity, PLoS Comput. Biol. 13 (2017), e1005751, Corollary 2. <https://arxiv.org/abs/1608.03993>
