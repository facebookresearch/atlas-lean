# Phenotypic proportions in multitype branching processes

**Model.** Cells of phenotypes $Y_1, \dots, Y_n$ live independent exponential lifetimes with rate $\alpha_i$ and are then replaced by random numbers $(d_{i1}, \dots, d_{in})$ of offspring of each phenotype (covering symmetric and asymmetric division, conversion and death), with $\mathbb E d_{ij}^2 < \infty$. The population vector $\vec X(t) \in \mathbb Z_{\ge 0}^n$ is a continuous-time multitype Markov branching process, and its mean $\vec x = \mathbb E\vec X$ (a row vector) satisfies

$$\frac{d\vec x}{dt} = \vec x A, \qquad a_{ii} = \alpha_i(\mathbb E d_{ii} - 1), \quad a_{ij} = \alpha_i\,\mathbb E d_{ij} \ \ (i \ne j).$$

The proportions $\vec p = \vec x/|\vec x|$ obey $\dot{\vec p} = \vec p\,\big[A - (\vec p\,\vec b^{\top}) I\big]$ with $\vec b^\top = A\vec 1^\top$, the vector of per-phenotype net growth rates $b_i = \sum_j a_{ij}$.

**Theorem 1 (validity of the Markov-chain model).** The proportions of the mean model satisfy the Kolmogorov forward equations $\dot{\vec p} = \vec p\,Q$ of an $n$-state Markov chain (with generator $Q$, rows summing to zero) if and only if

$$\sum_{j} a_{1j} = \sum_j a_{2j} = \cdots = \sum_j a_{nj} \ (= k),$$

i.e. all phenotypes have the same net growth rate; then $Q = A - kI$.

**Theorem 2 (deterministic phenotypic equilibrium).** Let $\lambda_1$ be the Perron eigenvalue of $A$ (real, with $\operatorname{Re}\mu < \lambda_1$ for all other eigenvalues $\mu$), assumed simple, and $\vec u$ its non-negative left eigenvector normalised to $\sum_i u_i = 1$. For all initial values outside a set of measure zero, $\vec x(t)e^{-\lambda_1 t} \to c\,\vec u$ with $c > 0$, so $\vec p(t) \to \vec u$, the unique stable fixed point of the proportion dynamics.

**Theorem 3 (stochastic phenotypic equilibrium).** Assume $\lambda_1$ is simple and positive. Conditioned on essential non-extinction (the population of phenotypes in the class supporting $\vec u$ does not die out), the stochastic proportions $P_i(t) = X_i(t)/|\vec X(t)|$ satisfy almost surely

$$\big(P_1(t), \dots, P_n(t)\big) \to \vec u \qquad (t \to \infty).$$

Moreover $u_i > 0$ exactly for the phenotypes reachable from the dominant communicating class, and $u_i > 0$, $a_{ij} > 0$ imply $u_j > 0$.

## Expansion

Differentiating $\vec p = \vec x/|\vec x|$ with $d|\vec x|/dt = \vec x\,\vec b^\top$ gives the proportion equation; its right-hand side is linear in $\vec p$ precisely when $\vec b$ is a constant vector, which gives Theorem 1, so Markov-chain fits to proportion data implicitly assume equal growth rates across phenotypes. Theorem 2 follows from the Perron–Frobenius decomposition $e^{At}$, dominated by $e^{\lambda_1 t}$ times the projection on the Perron eigenvector, since $A$ has non-negative off-diagonal entries. Theorem 3 uses the almost-sure convergence $\vec X(t)e^{-\lambda_1 t} \to W\vec u$ of supercritical multitype branching processes (Kesten–Stigum/Janson-type limit theorems) with $W > 0$ on non-extinction, here proved without requiring irreducibility of $A$, which allows irreversible phenotype transitions. The result extends to non-exponential lifetimes through age-dependent branching.

## Sources

- D.-Q. Jiang, Y. Wang, D. Zhou, "Phenotypic equilibrium as probabilistic convergence in multi-phenotype cell population dynamics", PLoS ONE 12 (2017) e0170916, Section 2 (branching-process model; deterministic model, Eq. 1), Section 3 (Eqs. 2–4, Theorem 1), Section 4 (Theorem 2; Lemmas 1–2; Theorem 3 with proof) and Section 6 (non-exponential lifetimes), <https://doi.org/10.1371/journal.pone.0170916> (PMC5300154).
