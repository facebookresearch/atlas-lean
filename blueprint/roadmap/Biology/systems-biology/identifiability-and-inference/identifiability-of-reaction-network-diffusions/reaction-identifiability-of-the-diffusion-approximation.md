# Reaction identifiability of the diffusion approximation

**Setting.** A reaction network $\mathcal{N} = (\mathcal{S}, \mathcal{C}, \mathcal{R})$ with mass-action rate constants $\kappa$ has diffusion approximation (chemical Langevin SDE)

$$dX_t = \sum_{y\to y'\in\mathcal{R}} \kappa_{y\to y'}X_t^{y}(y'-y)\,dt + \Bigl(\sum_{y\to y'}\kappa_{y\to y'}X_t^{y}(y'-y)(y'-y)^{\top}\Bigr)^{1/2} dW_t ,$$

so its law is determined by the drift and diffusion matrix. $\mathcal{N}$ is *reaction-identifiable* w.r.t. its SDE if distinct rate vectors give distinct SDE laws; two networks are *unconfoundable* if no choice of rate constants gives them the same law.

**Theorem.** Let $\mathcal{N}$ and $\mathcal{N}'$ share species, with $\mathcal{R} \ne \mathcal{R}'$.
1. $\mathcal{N}$ is reaction-identifiable w.r.t. its SDE iff, for every source complex $y$, the generalized reaction vectors

$$\bigl\{\bigl(y'-y,\ (y'-y)(y'-y)^{\top}\bigr) : y \to y' \in \mathcal{R}\bigr\}$$

are linearly independent.
2. $\mathcal{N}$ and $\mathcal{N}'$ are unconfoundable iff they have different source complexes, or the same source complexes and for **some** source $y$ the open cones

$$\operatorname{Cone}_{\mathcal{R}}(y) = \Bigl\{\sum_{y\to y'\in\mathcal{R}}\alpha_{y\to y'}\bigl(y'-y,(y'-y)(y'-y)^{\top}\bigr) : \alpha > 0\Bigr\}$$

and $\operatorname{Cone}_{\mathcal{R}'}(y)$ are disjoint. (The source's Theorem 3.3(2) says "for every source complex"; that is sufficient but not necessary. Matching laws requires, monomial by monomial, a common point of the two cones at every source $y$, and the rate constants at different sources can be chosen independently, so confoundability means that the cones meet at every source, and unconfoundability that they are disjoint at some source.)

**Linear conjugacy (Theorem 3.7).** There are rate constants for which $(\mathcal N,\kappa)$ and $(\mathcal N',\kappa')$ are linearly conjugate with respect to their SDEs (a linear bijection $h$ of $\mathbb R^n_{>0}$ carries the stopped solutions of one to those of the other, started at $h(x)$) iff there is $G = DP$, with $D$ a positive diagonal matrix and $P$ a permutation matrix, such that $\mathcal N$ and $\mathcal N'$ have the same complexes up to the permutation $P$ and, for every source complex $y$ of $\mathcal N$,

$$\operatorname{Cone}_{\mathcal R}(y)\cap\operatorname{Cone}^G_{\mathcal R'}(y)\ne\emptyset,\qquad \operatorname{Cone}^G_{\mathcal R'}(y)=\Bigl\{\sum_{y\to y'\in\mathcal R'}\alpha_{y\to y'}\bigl(G(y'-y),\,G(y'-y)(y'-y)^{\top}G^{\top}\bigr):\alpha>0\Bigr\}.$$

Because the diffusion matrix adds second-moment information, networks that are confoundable as deterministic ODEs can be identifiable as SDEs, while networks whose generalized reaction vectors are dependent keep non-identifiable rate constants.

## Expansion

The SDE law fixes, for each monomial $x^y$, the sum of $\kappa_{y\to y'}(y'-y)$ (drift) and of $\kappa_{y\to y'}(y'-y)(y'-y)^\top$ (diffusion). Distinct source complexes give linearly independent monomials, so the problem splits by source: rates are recoverable iff the combined vectors are independent, and two networks can mimic each other iff their positive cones intersect. The deterministic analogue uses only $y'-y$, which is why the stochastic criterion is weaker. Uniqueness of the law itself follows from strong existence and uniqueness up to the exit time of bounded open sets of the positive orthant and the martingale problem for the generator.

## Sources

- L. Faul, L. Hoessly, P. Xia, "Identifiability of SDEs for reaction networks", *European Journal of Applied Mathematics* 37(6) (2026), 1487–1505, Theorem 3.3, Theorem 3.7, Proposition 3.8, Theorems 5.2 and 5.4, <https://doi.org/10.1017/s0956792526100382> (preprint arXiv:2505.07638).
