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

**Split systems.** Let $\mathcal S$ be a split system on $X$ (a set of bipartitions $A|B$ of $X$ into non-empty parts), let $\mathcal C(\mathcal S)=\{A,B: A|B\in\mathcal S\}$ be its induced cluster system, and let $\mathbb L(\mathcal S)$ be the space of split weightings $\lambda:\mathcal S\to\mathbb R$. The split-based phylogenetic diversity game is $PD_\lambda(M)=\sum_{A|B\in\mathcal S:\ A\cap M\ne\emptyset,\ B\cap M\ne\emptyset}\lambda(A|B)$. For a linear map $\tau:\mathbb L(\mathcal S)\to\mathbb L(\mathcal C(\mathcal S))$ write $\Psi_\tau(FP)(\lambda)=FP(\tau(\lambda))$, with $FP$ the fair proportion index on $\mathcal C(\mathcal S)$. Then:

4. With the map $(\tau_1(\lambda))(C)=\tfrac12\,\lambda(C|X\setminus C)$ for $C\in\mathcal C(\mathcal S)$, $\Psi_{\tau_1}(FP)$ is a complete linear index on $\mathbb L(\mathcal S)$, $\sum_{x\in X}\Psi_{\tau_1}(FP)(\lambda)(x)=\sum_{S\in\mathcal S}\lambda(S)$, and

$$\big(\Psi_{\tau_1}(FP)(\lambda)\big)(x)=\sum_{A|B\in\mathcal S:\ x\in A}\frac{\lambda(A|B)}{2|A|},\qquad x\in X .$$

5. With the map $(\tau_2(\lambda))(A)=\frac{|B|}{|X|}\lambda(A|B)$ and $(\tau_2(\lambda))(B)=\frac{|A|}{|X|}\lambda(A|B)$ for $A|B\in\mathcal S$, the fair proportion index transports to the Shapley value of the split-based game:

$$FP(\tau_2(\lambda))=SV(PD_\lambda),\qquad \big(SV(PD_\lambda)\big)(x)=\sum_{A|B\in\mathcal S:\ x\in A}\frac{|B|}{|X|\,|A|}\,\lambda(A|B).$$

The two maps differ, and so do the two indices: for $X=\{a,b,c\}$ and the single split $\{a\}|\{b,c\}$ of weight $1$, item 4 gives $(1/2,1/4,1/4)$ while item 5 gives $(2/3,1/6,1/6)$.

## Proof sketch

The game $g_C$ is a unanimity-type game in which a coalition gains $1$ as soon as it touches $C$. By symmetry every member of $C$ is pivotal with the same probability and non-members are null players, so $SV(g_C)(x)=\mathbf 1[x\in C]/|C|$. Linearity of the Shapley value in $g$ and the decomposition $PD_\omega=\sum_C\omega(C)g_C$ then give $SV(PD_\omega)=FP(\omega)$. This extends the classical rooted-tree identity (fair proportion equals the Shapley value of the phylogenetic diversity game) to arbitrary, non-hierarchical cluster systems. The uniqueness statement must be phrased on the subspace $\mathbb{PD}(\mathcal C)$, since that is in general a proper subspace of all games. In the split case, $\tau_1$ shares each split weight equally between its two sides, which produces the factor $1/(2|A|)$ and completeness; $\tau_2$ gives side $A$ the share $|B|/|X|$, and by linearity it suffices to check one split of weight $1$, where both sides of item 5 equal $|B|/(|X||A|)$ for $x\in A$.

## Sources

- V. Moulton, A. Spillner and K. Wicke, "Phylogenetic Diversity Indices from an Affine and Projective Viewpoint", *Bulletin of Mathematical Biology* 86 (2024), 103, <https://doi.org/10.1007/s11538-024-01332-x>. Preprint version: arXiv:2403.15842 (2024), Lemma 2.1 (fair proportion is complete and linear), Lemma 4.1 (dimension of $\mathbb{PD}(\mathcal C)$), Theorem 4.3 (characterization of the Shapley value), Corollary 4.4 (fair proportion equals Shapley value), Theorem 5.1 (fair proportion transported by $\tau_2$ is the split Shapley value, eqs. (14)–(16)), Corollary 6.2 (split-system formula for $\tau_1$, eqs. (17)–(18)), <https://doi.org/10.48550/arXiv.2403.15842>.
