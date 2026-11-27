# Fair proportion index equals the Shapley value on cluster systems

**Setting.** Let $X$ be a finite set of species and $\mathcal C\subseteq\mathcal P(X)\setminus\{\emptyset\}$ a *cluster system* on $X$ (for a rooted phylogenetic tree, $\mathcal C$ is the set of leaf sets below its edges). A *weighting* is any $\omega:\mathcal C\to\mathbb R$; write $\mathbb L(\mathcal C)$ for the space of weightings. The *fair proportion index* is

$$(FP(\omega))(x)=\sum_{C\in\mathcal C:\ x\in C}\frac{\omega(C)}{|C|},\qquad x\in X .$$

The weighting $\omega$ induces the *phylogenetic diversity game*

$$PD_\omega(M)=\sum_{C\in\mathcal C:\ M\cap C\neq\emptyset}\omega(C),\qquad M\subseteq X,$$

and $\mathbb{PD}(\mathcal C)=\{PD_\omega:\omega\in\mathbb L(\mathcal C)\}$ is a linear subspace of $\mathbb R^{\mathcal P(X)}$ of dimension $|\mathcal C|$. The *Shapley value* of a game $g$ is

$$(SV(g))(x)=\frac1{|X|!}\sum_{M\ni x}(|M|-1)!\,(|X|-|M|)!\,\big(g(M)-g(M\setminus\{x\})\big).$$

**Theorem.** For every cluster system $\mathcal C$ on $X$:

1. The fair proportion index is linear and *complete*: $\sum_{x\in X}(FP(\omega))(x)=\sum_{C\in\mathcal C}\omega(C)$.
2. On $\mathbb{PD}(\mathcal C)$, the Shapley value is the unique map $\mathbb{PD}(\mathcal C)\to\mathbb R^X$ that is additive, Pareto efficient ($\sum_x \Phi(g)(x)=g(X)$) and group proportional.
3. For every $\omega\in\mathbb L(\mathcal C)$,

$$FP(\omega)=SV\Big(\sum_{C\in\mathcal C}\omega(C)\,g_C\Big)=SV(PD_\omega),$$

where $g_C(M)=1$ if $M\cap C\neq\emptyset$ and $0$ otherwise.

**Split systems.** If $\mathcal S$ is a split system on $X$ with split weights $\lambda$, transporting the fair proportion index from the induced cluster system through the natural linear map $\tau$ gives a complete linear index on $\mathbb L(\mathcal S)$ with

$$\big(\Psi_\tau(FP)(\lambda)\big)(x)=\sum_{A|B\in\mathcal S:\ x\in A}\frac{\lambda(A|B)}{2|A|},$$

which coincides with the Shapley value of the split-based phylogenetic diversity game.

## Proof sketch

The game $g_C$ is a unanimity-type game in which a coalition gains $1$ as soon as it touches $C$. By symmetry every member of $C$ is pivotal with the same probability and non-members are null players, so $SV(g_C)(x)=\mathbf 1[x\in C]/|C|$. Linearity of the Shapley value in $g$ and the decomposition $PD_\omega=\sum_C\omega(C)g_C$ then give $SV(PD_\omega)=FP(\omega)$. This extends the classical rooted-tree identity (fair proportion equals the Shapley value of the phylogenetic diversity game) to arbitrary, non-hierarchical cluster systems. The uniqueness statement must be phrased on the subspace $\mathbb{PD}(\mathcal C)$, since that is in general a proper subspace of all games. In the split case, each split weight is shared equally between its two sides, which produces the factor $1/(2|A|)$.

## Sources

- V. Moulton, A. Spillner and K. Wicke, "Phylogenetic Diversity Indices from an Affine and Projective Viewpoint", *Bulletin of Mathematical Biology* 86 (2024), 103, <https://doi.org/10.1007/s11538-024-01332-x>. Preprint version: arXiv:2403.15842 (2024), Lemma 2.1 (fair proportion is complete and linear), Lemma 4.1 (dimension of $\mathbb{PD}(\mathcal C)$), Theorem 4.3 (characterization of the Shapley value), Corollary 4.4 (fair proportion equals Shapley value), Corollary 6.2 (split-system formula), <https://doi.org/10.48550/arXiv.2403.15842>.
