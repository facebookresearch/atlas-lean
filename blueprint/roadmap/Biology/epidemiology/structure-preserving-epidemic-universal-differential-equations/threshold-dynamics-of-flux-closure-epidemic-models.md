# Threshold dynamics of flux-closure epidemic models

**Admissible closures.** Start from a mechanistic compartmental model $\dot x=f(x,\theta)$ on $\mathbb R^n_{\ge0}$ that is $C^2$, quasi-positive ($f_i\ge0$ when $x_i=0$) and dissipative ($\mathbf 1^{\mathsf T}f\le\Lambda-\mu\mathbf 1^{\mathsf T}x$). Adding a generic learned correction $\mathcal N_\phi(x)$ breaks positivity whenever some $F_i(\bar x)<0$ at a boundary point with $\bar x_i=0$. Instead, an **admissible closure** adds learned rates only as fluxes: each learned rate $G_{\phi,k}(x)\ge0$ moves mass out of a source compartment $s_k$, either into a target or out of the system ($\nu_k\in\{e_{t_k}-e_{s_k},-e_{s_k}\}$), and is proportional to $x_{s_k}$. Transmission takes the form $(\hat w-e_{s_*})\,x_{s_*}\lambda_\phi(x)$ with force of infection $\lambda_\phi(x)=\sum_{j\in\mathcal I}\beta^\phi_j(x)\,y_j$ factorized through the infected coordinates $y$; every $C^3$ $\lambda$ vanishing at $y=0$ admits this Hadamard factorization, $\beta_j=\int_0^1\partial_{y_j}\lambda(z,\tau y)\,d\tau$.

**Theorem (well-posedness and invariance).** The resulting universal differential equation is $C^2$ with unique solutions; $\mathbb R^n_{\ge0}$ is forward invariant (interior stays interior); solutions are global with $N(t)\le N(0)e^{-\mu t}+\frac\Lambda\mu(1-e^{-\mu t})$, so $\Omega=\{x\ge0:\mathbf 1^{\mathsf T}x\le\Lambda/\mu\}$ is absorbing; the disease-free set $\{y=0\}$ is invariant.

**Theorem (rank-one next-generation matrix).** If the disease-free subsystem has a unique globally stable equilibrium $E_0$ with susceptible level $z^*_{s_*}>0$ and the transfer matrix $V(\phi)$ is a nonsingular M-matrix, then $F(\phi)=z^*_{s_*}\,w\,\beta^\phi(E_0)^{\mathsf T}$ has rank one and

$$\mathcal R_0(\phi)=\rho\big(F(\phi)V(\phi)^{-1}\big)=z^*_{s_*}\,\beta^\phi(E_0)^{\mathsf T}\,V(\phi)^{-1}w ,$$

which depends on the learned transmission closure only through its value at $E_0$. For the neural SEIR model $\dot S=\Lambda-\beta_\phi(x)SI-\mu S$, $\dot E=\beta_\phi SI-(\mu+\sigma)E$, $\dot I=\sigma E-(\mu+\gamma+\delta)I$, $\dot R=\gamma I-\mu R$, this gives $\mathcal R_0=\frac{\sigma\Lambda\beta_\phi(E_0)}{\mu(\mu+\sigma)(\mu+\gamma+\delta)}$. Monotonicity: $\beta^-\le\beta^\phi(E_0)\le\beta^+$ sandwiches $\mathcal R_0$.

**Theorem (thresholds).** $E_0$ is locally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$; under a uniform domination condition it is globally stable with exponential extinction when $\mathcal R_0<1$. If $\mathcal R_0>1$ an endemic equilibrium exists, unique under a sublinearity condition on the frozen force of infection; and if $F-V$ is irreducible the infection is uniformly persistent. For the separable SIR subclass with $h_\phi(I)/I$ nonincreasing, the endemic equilibrium is globally stable.

**Theorem (bifurcation direction).** For the neural SEIR model with prevalence-dependent $\beta_\phi(I)$, center-manifold analysis at $\mathcal R_0=1$ gives a backward bifurcation if

$$\frac{\beta_\phi'(0)}{\beta_\phi(0)}>\frac{(\mu+\sigma)(\mu+\gamma+\delta)}{\sigma\Lambda}$$

and a forward one under the reverse strict inequality; any nonincreasing dependence on prevalence yields a forward bifurcation.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)
- [SEIR epidemic model](../seir-epidemic-model/README.md)

## Expansion

Positivity follows because every learned flux leaving compartment $i$ carries a factor $x_i$, so it vanishes on $\{x_i=0\}$ and quasi-positivity is preserved; dissipativity holds because learned fluxes only move or remove mass. Factorizing the force of infection through infected classes makes the infection block of the Jacobian at $E_0$ equal to $F-V$ with $F$ an outer product, so the Jacobian is block triangular and $\mathcal R_0$ is the single non-zero eigenvalue of the next-generation matrix; the M-matrix lemma ($s(F-V)$ and $\rho(FV^{-1})-1$ have equal signs) gives the local threshold. Endemic equilibria correspond to fixed points of the frozen-force map $H(\lambda)=\lambda_\phi(x(\lambda))$ with $H'(0)=\mathcal R_0$; an intermediate-value argument gives existence and sublinearity gives uniqueness. The backward-bifurcation coefficient from Castillo-Chavez-Song center-manifold theory involves the derivatives of the learned rate at $E_0$.

## Sources

- A. Alsammani, M. Martcheva, "Structure-preserving universal differential equations for epidemic dynamics", arXiv:2611.23291 (2026), Section 3 (Assumptions 3.1-3.3, Proposition 3.4, Definition 3.5, Assumption 3.6, Proposition 3.7, Examples), Section 4 (Theorems 4.3-4.6), Section 5 (Propositions 5.1, 5.5, Definition 5.7, Theorems 5.8-5.9), Sections 6-8 (Theorems 6.5, 6.7, 7.2, 7.6, 7.8, 8.1) and Section 9 (Theorem 9.1, Corollary 9.2), <https://doi.org/10.48550/arXiv.2611.23291>.
