# Time-dependent product-form Poisson distributions and dynamical restricted complex balance

**Setting.** Consider a reaction network with species $S_1, \dots, S_d$, complexes $y \in \mathbb{Z}_{\ge 0}^d$ and reactions $y_k \to y_k'$ with rate constants $\kappa_k > 0$. The stochastic model $X_t$ uses mass-action intensities $\lambda_k(x) = \kappa_k \frac{x!}{(x - y_k)!}$, and the deterministic model is $\dot c = \sum_k \kappa_k c^{y_k}(y_k' - y_k)$, with $c^{y} = \prod_i c_i^{y_i}$.

**Definition (DR condition).** A deterministic solution $c(t)$ satisfies the *dynamical and restricted complex balance* condition if for every complex $z$ with $\|z\|_1 \ge 2$ and every $t \ge 0$,

$$\sum_{k : y_k = z}\kappa_k c(t)^{z} = \sum_{k : y_k' = z}\kappa_k c(t)^{y_k}.$$

(Only complexes of molecularity at least two must balance, and only along the trajectory.) Along such a trajectory the mass-action vector field is linear and $c(t)$ stays positive.

**Theorem.** Suppose $X_0$ has the product-Poisson law $\mu(x) = \prod_{i=1}^d e^{-\tilde c_i}\tilde c_i^{x_i}/x_i!$ with $\tilde c \in \mathbb{R}^d_{>0}$. The following are equivalent:
1. the solution of the deterministic mass-action system with $c(0) = \tilde c$ satisfies the DR condition;
2. the law of $X_t$ is a product of Poissons, $P(X_t = x) = \prod_i e^{-c_i(t)}c_i(t)^{x_i}/x_i!$ for all $t \ge 0$, for some deterministic $c(t)$ with $c(0) = \tilde c$;
3. the same holds with $c(t)$ the solution of the deterministic mass-action system started at $\tilde c$.

Moreover, if the law of $X_t$ is a product of Poissons with parameter $c(t)$, then necessarily $\mathbb{E}[X_t] = c(t)$ solves the deterministic equation. For binary networks ($\|y\|_1 \le 2$ for all complexes), DR holds along $u(t)$ iff $B(u(t)) = 0$, where $B_{ij}(u) = \sum_k \kappa_k u^{y_k}\big(y'_{ki}y'_{kj} - y_{ki}y_{kj} - \delta_{ij}(y'_{ki} - y_{ki})\big)$ is the diffusion matrix of Gardiner's Poisson representation. For a one-species network, a nontrivial time-dependent Poisson solution exists from a Poisson start iff the network is first order, with complexes $\{\emptyset, S_1\}$.

## Proof sketch

Insert the product-Poisson ansatz into the chemical master equation. Dividing by the Poisson weight, the equation holds iff $c(t)$ solves the mass-action ODE and $\sum_k \kappa_k c^{y_k}[g_{x,c}(y_k') - g_{x,c}(y_k)] = 0$ for all $x$, where $g_{x,c}(y) = \sum_j (x_j/c_j - 1)y_j - \frac{x!}{(x-y)!}c^{-y} + 1$ vanishes identically for complexes of order $0$ and $1$. The functions $x \mapsto g_{x,c}(z)$ for distinct complexes with $\|z\|_1 \ge 2$ are linearly independent, so the residual vanishes iff the coefficient of each such complex, the in-flow minus the out-flow at $z$, is zero: the DR condition. Stationary complex balance is the special case $c(t) \equiv c$, recovering the classical product-Poisson stationary law.

## Sources

- David F. Anderson, David Schnoerr and Chaojie Yuan, "Time-dependent product-form Poisson distributions for reaction networks with higher order complexes", *Journal of Mathematical Biology* 80 (2020), 1919–1951, <https://doi.org/10.1007/s00285-020-01485-y>. Preprint version: arXiv:1904.11583 (2019), Definition of the DR condition (Section 2), Lemma 2.1, Theorem 3.1, Lemmas 3.1 and 3.2, Propositions 3.1 and 4.1, <https://doi.org/10.48550/arXiv.1904.11583>.
