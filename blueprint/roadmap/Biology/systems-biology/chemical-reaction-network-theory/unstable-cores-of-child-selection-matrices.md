# Unstable cores of Child-Selection matrices

Let $\Gamma=(M,E)$ be a chemical reaction network with species set $M$, reaction set $E$, reactant coefficients $s^j_m\ge 0$, product coefficients $\tilde s^j_m\ge 0$ and stoichiometric matrix $S_{mj}=\tilde s^j_m-s^j_m$. Concentrations evolve by $\dot x=S\,r(x)$, where each rate $r_j$ depends only on the reactants of $j$ and is strictly increasing in each of them for $x>0$. The network is assumed consistent: $S$ has a strictly positive kernel vector. A kinetic model is *parameter-rich* if, at every positive equilibrium $\bar x$, every reactivity matrix $R$ with $R_{jm}>0$ exactly when $s^j_m>0$ (and $R_{jm}=0$ otherwise) is realized as $R_{jm}=\partial r_j/\partial x_m(\bar x)$ by some choice of parameters (Michaelis-Menten and generalized mass action are parameter-rich, Lemmas 5 and 6). The Jacobian at $\bar x$ is then $G=SR$. The network *admits instability* if some choice of parameters gives a positive equilibrium whose Jacobian is Hurwitz-unstable, that is, has an eigenvalue with positive real part.

A *$k$-Child-Selection triple* is $\boldsymbol\kappa=(\kappa,E_\kappa,J)$ with $\kappa\subseteq M$, $E_\kappa\subseteq E$, $|\kappa|=|E_\kappa|=k$, and a bijection $J:\kappa\to E_\kappa$ such that $m$ is a reactant of $J(m)$ ($s^{J(m)}_m>0$) for every $m\in\kappa$. Its *Child-Selection matrix* is the $k\times k$ matrix

$$S[\boldsymbol\kappa]_{ml}=\tilde s^{J(l)}_m-s^{J(l)}_m,\qquad m,l\in\kappa,$$

so that $\det S[\boldsymbol\kappa]=\operatorname{sgn}(J)\det S[\kappa,E_\kappa]$.

**Instability from a Child-Selection matrix.** For a network with a parameter-rich kinetic model, if some Child-Selection matrix $S[\boldsymbol\kappa]$ is Hurwitz-unstable, then the network admits instability.

**Unstable cores.** An *unstable core* is a Hurwitz-unstable Child-Selection matrix none of whose proper principal submatrices is Hurwitz-unstable. Every unstable core is an irreducible matrix. An unstable core of size $k$ is an *unstable-positive feedback* if $\operatorname{sign}\det S[\boldsymbol\kappa]=(-1)^{k-1}$ and an *unstable-negative feedback* if $\operatorname{sign}\det S[\boldsymbol\kappa]=(-1)^k$. An unstable-positive feedback has exactly one real positive eigenvalue; an unstable-negative feedback has none. Moreover, for an unstable-positive feedback the associated elementary Cauchy-Binet component $G[\boldsymbol\kappa]=S[\boldsymbol\kappa]R[\boldsymbol\kappa]$ satisfies $\operatorname{sign}\det G[\boldsymbol\kappa]=(-1)^{k-1}$ and is therefore unstable for every choice of positive reactivities.

The authors conjecture the converse direction for the weaker notion of D-unstable cores (Child-Selection matrices $A$ with $AD$ Hurwitz-unstable for some positive diagonal $D$, minimal among principal submatrices): a network with no D-unstable core does not admit instability.

## Expansion

The coefficients of the characteristic polynomial of $G=SR$ expand by Cauchy-Binet into sums over $k$-Child-Selection triples of $\det S[\boldsymbol\kappa]\det R[\boldsymbol\kappa]$-type terms. Parameter richness lets one scale the reactivities $r'_{J(m)m}$ for $m\in\kappa$ to be large and all others small; in this limit the spectrum of $G$ approaches that of $S[\boldsymbol\kappa]$ times a positive diagonal matrix together with $|M|-k$ near-zero eigenvalues, and continuity of polynomial roots transfers instability of the selected block to the full Jacobian. Minimality in the definition of an unstable core isolates the smallest such blocks, and the sign of the determinant separates the real-eigenvalue (saddle-node type) case from the oscillatory one.

## Sources

- N. Vassena and P. F. Stadler, "Unstable Cores are the source of instability in chemical reaction networks", *Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences* 480(2285) (2024), 20230694, Definition 7 ($k$-Child-Selection triple), Section 4 (Child-Selection matrices), Lemmas 5-6, Lemma 11, Corollary 12, Corollary 14, Definition 15 (unstable core), Observation 16, Definition 17 (D-unstable core), Conjecture 18, Definition 19, Observation 20 and Lemma 21, <https://doi.org/10.1098/rspa.2023.0694> (preprint arXiv:2308.11486).
