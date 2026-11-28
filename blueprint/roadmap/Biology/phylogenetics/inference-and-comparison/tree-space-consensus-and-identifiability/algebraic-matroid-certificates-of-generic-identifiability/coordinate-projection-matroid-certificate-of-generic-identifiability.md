# Coordinate projection matroid certificate of generic identifiability

**Generic identifiability.** For algebraic models $M_1,\dots,M_k$ in the probability simplex $\Delta_r$ (for instance the images of phylogenetic Markov models on different trees), the discrete parameter $s\in[k]$ is *generically identifiable* if $\dim(M_{s_1}\cap M_{s_2})<\min(\dim M_{s_1},\dim M_{s_2})$ for all $s_1\ne s_2$.

**Coordinate projection matroid.** For an irreducible variety $V\subset k^n$ and $S\subseteq[n]$ let $\pi_S$ be the coordinate projection. The sets $S$ with $\overline{\pi_S(V)}=k^{|S|}$ are the independent sets of a matroid $\mathcal M(V)$; equivalently $S$ is independent iff the vanishing ideal $P$ of $V$ satisfies $P\cap k[x_i:i\in S]=\langle0\rangle$. If $V=\overline{\phi(k^d)}$ for a polynomial parametrization $\phi$, then $\mathcal M(V)$ is the linear matroid of the columns of the transposed Jacobian $J(\phi)=(\partial\phi_j/\partial\theta_i)$ over $k(\theta)$, and (in characteristic zero) also the linear matroid of $J(\phi)$ evaluated at generic parameter values.

**Proposition (matroid certificate).** Let $M_1,M_2\subset\Delta_r$ be irreducible algebraic models with $\dim M_1\ge\dim M_2$. If some set of coordinates $S$ satisfies

$$S\in\mathcal M(M_2)\setminus\mathcal M(M_1),$$

then $\dim(M_1\cap M_2)<\min(\dim M_1,\dim M_2)$.

**Randomized certification.** If $S$ is independent for $J(\phi)$ over $k(\theta)$ and a non-vanishing $|S|\times|S|$ minor has degree $\alpha$, then for parameters drawn uniformly from a finite $E\subseteq k$ with $|E|>\alpha$, the probability that $S$ is dependent in the specialized Jacobian is at most $\alpha/|E|$ (Schwartz–Zippel). Random subsets $S$ with $|S|\le\dim M_2$ tested on numerical Jacobians therefore yield certificates with error probability as small as desired.

## Expansion

Identifiability follows from polynomials $f_1\in I(M_1)\setminus I(M_2)$ and $f_2\in I(M_2)\setminus I(M_1)$. If $\dim M_1>\dim M_2$, some $f_2$ exists automatically; independence of $S$ on $M_2$ and dependence on $M_1$ mean $I(M_1)\cap k[S]\ne0=I(M_2)\cap k[S]$, which supplies $f_1$. If the dimensions are equal, $S$ shows $M_1\ne M_2$, and two distinct irreducible varieties of equal dimension meet in lower dimension. The certificate proves the separating polynomials exist without computing them; it is weaker than comparing ideals, since distinct ideals can share a matroid (two 4-leaf 4-cycle CFN network models have different principal ideals but the same matroid).

## Sources

- B. Hollering, S. Sullivant, "Identifiability in phylogenetics using algebraic matroids", arXiv:1909.13754 (2019), <https://doi.org/10.48550/arXiv.1909.13754>. Section 2 (Definitions 2.1, 2.5, 2.7; Propositions 2.2, 2.6, 2.8) and Section 3 (Propositions 3.1, 3.2; Algorithms 3.3, 3.6; Lemma 3.4; Corollary 3.5); Example 5.11.
