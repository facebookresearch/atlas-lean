# Closest stochastic point to a quartet distribution with a non-stochastic interior edge

**Setting.** Let $\mathcal T=\{12|34,\,13|24,\,14|23\}$ be the unrooted quartet topologies on four leaves, with nucleotide alphabet $\Sigma=\{\mathtt A,\mathtt C,\mathtt G,\mathtt T\}$. For $T\in\mathcal T$, a root distribution $\pi$ and $4\times4$ transition matrices $M_1,\dots,M_4$ on the pendant edges and $M_5$ on the interior edge, the hidden Markov process on $T$ gives a joint distribution $\psi_T(\pi,\{M_i\})\in\mathbb R^{4^4}$ of leaf characters. The *stochastic phylogenetic region* $\mathcal V_T^+$ is the image of $\psi_T$ over stochastic parameters (nonnegative entries, rows summing to $1$); the *phylogenetic variety* $\mathcal V_T$ is the Zariski closure of $\psi_T$ over all real parameters with rows summing to $1$, so $\mathcal V_T^+\subsetneq\mathcal V_T$. Distances are Euclidean.

For a real matrix $M$, its *closest stochastic matrix* $\widehat M$ is the unique minimizer of $\|M-X\|_F$ over stochastic $X$; equivalently each row of $\widehat M$ is the Euclidean projection of the corresponding row of $M$ onto the standard simplex $\Delta$. The projection $\widehat{\mathbf x}$ of $\mathbf x\in\mathbb R^N$ equals the vertex $\mathbf p_i$ if and only if $x_i-x_j\ge1$ for all $j\ne i$, and commutes with coordinate permutations. A *K81* (Kimura 3-parameter) matrix has rows $(a,b,c,d),(b,a,d,c),(c,d,a,b),(d,c,b,a)$ with $a+b+c+d=1$; a JC69 matrix ($b=c=d$) is stochastic if and only if its eigenvalues lie in $[-1/3,1]$.

**Proposition.** Let $P=\psi_T(\mathrm{Id},\mathrm{Id},\mathrm{Id},\mathrm{Id},M)$ with $M$ a non-stochastic K81 matrix and $T$ any quartet tree, and let $P_T^+$ be a closest point to $P$ in $\mathcal V_T^+$. Then

1. $P_T^+=\psi_T(\mathrm{Id},\mathrm{Id},\mathrm{Id},\mathrm{Id},\widehat M)$; it is also the closest point to $P$ in the whole simplex $\Delta\subset\mathbb R^{4^4}$, and it is unique;
2. for every $T'\ne T$ in $\mathcal T$, $d(P,\mathcal V_{T'}^+)\ge d(P,\mathcal V_T^+)$;
3. equality holds in (2) if and only if $P_T^+\in\mathcal V_T^+\cap\mathcal V_{T'}^+$, if and only if $\widehat M$ is a permutation matrix.

**Theorem (robustness).** Let $M$ be a non-stochastic K81 matrix such that $\widehat M$ is not a permutation matrix, $P_0=\psi_T(\mathrm{Id},\mathrm{Id},\mathrm{Id},\mathrm{Id},M)$ and $T'\in\mathcal T\setminus\{T\}$. Every $P\in\mathbb R^{4^4}$ with

$$
d(P,P_0)<\frac{d(P_0,\mathcal V_{T'}^+)-d(P_0,\mathcal V_T^+)}{2}
$$

satisfies $d(P,\mathcal V_T^+)<d(P,\mathcal V_{T'}^+)$.

## Expansion

Data generated on $T$ with very short external branches but a non-stochastic interior matrix lie on $\mathcal V_T$ but off $\mathcal V_T^+$. Since $\mathcal V_T^+\subset\Delta$, $d(P,\mathcal V_T^+)\ge d(P,\widehat P)$; with identity pendant matrices the coordinates of $P$ are, up to the root distribution, the entries of $M$, so projecting onto $\Delta$ reduces to projecting each row of $M$ onto the simplex, and the result $\psi_T(\ldots,\widehat M)$ is already in $\mathcal V_T^+$, giving (1). For $T'$ the same bound is attained only when the projected point is also realizable on $T'$, which forces $\widehat M$ to be a permutation matrix. The theorem follows from the triangle inequality: $Q\mapsto d(Q,\mathcal V_{T'}^+)-d(Q,\mathcal V_T^+)$ is $2$-Lipschitz and positive at $P_0$. So, near such points, choosing the tree whose stochastic region is closest recovers the true topology.

## Proof depends on

- [The distance to a set is 1-Lipschitz](../../../../Topology/metric-spaces/distance-to-a-set.md)

## Sources

- Marta Casanellas, Jesús Fernández-Sánchez, Marina Garrote-López. *Distance to the stochastic part of phylogenetic varieties* (2019), Sections 2–4 and 6: Definition 3.1, Lemmas 3.2 and 3.4, Proposition 4.1, Theorem 4.3, Theorem 6.3, Conjecture 6.4 and Theorem 6.6. <https://doi.org/10.48550/arXiv.1912.02138>
