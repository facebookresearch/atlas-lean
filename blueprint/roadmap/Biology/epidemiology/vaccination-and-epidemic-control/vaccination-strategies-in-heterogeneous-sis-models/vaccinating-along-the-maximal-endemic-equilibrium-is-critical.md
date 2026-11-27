# Vaccinating along the maximal endemic equilibrium is critical

Let $(\Omega,\mu)$ be a probability space of individual features, such as age or activity level, and $k\ge0$ a transmission kernel with a boundedness condition $\sup_x\|k(x,\cdot)\|_{L^q}<\infty$ for some $q>1$. The heterogeneous SIS model of Lajmanovich–Yorke type follows the vector field

$$
F(g)=(1-g)\,T_k(g)-\gamma g,\qquad T_k(g)(x)=\int_\Omega k(x,y)g(y)\,\mu(dy),
$$

on $\Delta=\{g:\Omega\to[0,1]\ \text{measurable}\}$, where $u_t(x)$ is the probability that an individual of feature $x$ is infected. Then $R_0=\rho(T_{k/\gamma})$, and there is a maximal equilibrium $\mathfrak g$ that dominates all equilibria, with $\mathfrak g\neq0$ iff $R_0>1$. A vaccination strategy $\eta:\Omega\to[0,1]$ is the fraction left unvaccinated at each feature. Its effective reproduction number is $R_e(\eta)=\rho(T_{k\eta/\gamma})$, the spectral radius of the operator with kernel $k(x,y)\eta(y)/\gamma$, and $\eta$ achieves herd immunity when $R_e(\eta)\le1$.

**Theorem.** If $R_0\ge1$, the strategy $\eta^\star=1-\mathfrak g$ (vaccinate each feature class in proportion to its endemic prevalence) is critical:

$$
R_e(1-\mathfrak g)=1.
$$

**Characterization of maximality.** For an equilibrium $h$ (so $F(h)=0$), the following are equivalent: (i) $h=\mathfrak g$; (ii) the spectral bound satisfies $s(DF[h])\le0$; (iii) $R_e((1-h)^2)\le1$; (iv) the disease-free state of the model vaccinated with $1-h$ is linearly stable, $s(DF_{1-h}[0])\le0$; (v) $R_e(1-h)\le1$. So an equilibrium fails to be maximal exactly when it is linearly unstable.

Example: in an age-structured population with $R_0=2$ and contact rates fitted to social activity, this strategy needs about 29% fewer doses than vaccinating a uniform fraction $1-1/R_0$.

## Depends on

- [Spectral bound and reproduction number for infinite-dimensional structured models](../../next-generation-matrix-and-the-basic-reproductio/spectral-bound-and-reproduction-number-for-infinite-dimensional-structure.md)

## Proof sketch

At the maximal equilibrium, $T_k(\mathfrak g)=\gamma\mathfrak g/(1-\mathfrak g)$. So $\mathfrak g$ is a positive eigenfunction with eigenvalue $1$ of the operator with kernel $k(x,y)(1-\mathfrak g(x))/\gamma$, which has the same spectral radius as $T_{k(1-\mathfrak g)/\gamma}$; this gives $R_e\ge1$. A Collatz–Wielandt type lemma shows that $T_k(g)>\lambda g$ on $\{g>0\}$ forces $\rho(T_k)>\lambda$. Combined with the fact that any $g$ with $F_\eta(g)\ge0$ is dominated by the maximal equilibrium of the vaccinated model, this excludes $R_e(1-\mathfrak g)>1$.

## Sources

- Jean-François Delmas, Dylan Dronnier and Pierre-André Zitt, "Vaccinating According to the Maximal Endemic Equilibrium Achieves Herd Immunity", *SIAM Journal on Applied Mathematics* 85 (2025), 806–820, <https://doi.org/10.1137/23m1558112>. Preprint version: arXiv:2211.15463 (2022), Section 2 (vector field (eq:vec-field)), Theorem 4.1, Lemmas 4.2–4.3, Proposition 4.4, <https://doi.org/10.48550/arXiv.2211.15463>.
