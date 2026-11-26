# A degree-theory criterion for unique versus multiple equilibria

Let a reaction network with stoichiometric matrix $N$ of rank $s$ have rate functions satisfying Eq. (2) of Conradi, Feliu, Mincheva and Wiuf (2017), let $W$ be a matrix in reduced row echelon form whose $d$ rows form a basis of the left kernel of $N$, with pivot (first nonzero) columns $i_1 < \dots < i_d$, and let $\varphi_c$ be the map (Eq. (6) of the source) whose $i$-th component is the species-formation rate of species $i$ for $i \notin \{i_1, \dots, i_d\}$ and, for $i = i_j$, the $j$-th component of $Wx - c$; its Jacobian $M(x)$ does not depend on $c$. These choices fix the sign of $\det M(x)$: replacing a conservation equation by its negative leaves the zeros of $\varphi_c$ unchanged but reverses the sign of the determinant. Theorem 1 of the source states, for a stoichiometric compatibility class $P_c$ with positive points, a dissipative network, and no boundary equilibria in $P_c$: (A′) if $\operatorname{sign}\det M(x) = (-1)^s$ at all positive equilibria in $P_c$, there is exactly one positive equilibrium in $P_c$, and it is non-degenerate; (B′) if $\operatorname{sign}\det M(x) = (-1)^{s+1}$ at some positive equilibrium in $P_c$, there are at least two positive equilibria in $P_c$, at least one non-degenerate, and at least three, always an odd number, if all are non-degenerate. Corollary 2 restates this when the positive equilibria admit a positive parametrization $\Phi$, with $a(\hat x) = \det M(\Phi(\hat x))$, for a dissipative network with no boundary equilibria in any stoichiometric compatibility class with positive points: if $\operatorname{sign} a = (-1)^s$ everywhere there is exactly one positive equilibrium in each class with positive points, and if $\operatorname{sign} a(\hat x) = (-1)^{s+1}$ for some $\hat x$ the class through $\Phi(\hat x)$ is multistationary. The proof relates $\det M(x)$ to the Brouwer degree of $\varphi_c$ at $0$.

## Expansion

1. The model: rate functions satisfying Eq. (2), dissipativity, boundary equilibria, the row-reduced matrix $W$, the map $\varphi_c$ (Eq. (6)) with the pivot rows replaced, and non-degenerate equilibria.
2. Theorem 1 and Corollary 1, with the Brouwer degree argument of the supporting information.
3. Positive parametrizations of the equilibrium set, the function $a$ (Eq. (10)) and Corollary 2.
4. The procedure of the source for finding parameter regions of mono- and multistationarity, and its applications, as separate statements.

## Sources

- C. Conradi, E. Feliu, M. Mincheva and C. Wiuf, Identifying parameter regions for multistationarity, PLoS Comput. Biol. 13 (2017), e1005751, Theorem 1 and Corollaries 1 and 2. <https://arxiv.org/abs/1608.03993>
