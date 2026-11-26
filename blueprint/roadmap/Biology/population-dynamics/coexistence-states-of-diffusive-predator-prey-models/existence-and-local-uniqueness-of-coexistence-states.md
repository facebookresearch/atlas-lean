# Existence and local uniqueness of coexistence states of diffusive predator–prey models

Let $\Omega\subset\mathbb{R}^N$ be a bounded $\mathcal C^2$ domain and consider the stationary diffusive Lotka–Volterra predator–prey problem

$$
\mathscr L_1u=\lambda u-a(x)u^2-b(x)uv,\qquad \mathscr L_2v=\mu v-d(x)v^2+c(x)uv\quad\text{in }\Omega,\qquad \mathscr B_1u=\mathscr B_2v=0\ \text{on }\partial\Omega .
$$

Here $u$ is the prey and $v$ the predator. The operators $\mathscr L_\kappa=-\operatorname{div}(A_\kappa\nabla)+\langle b_\kappa,\nabla\rangle+c_\kappa$ are uniformly elliptic with $A_\kappa$ symmetric with $W^{1,\infty}$ entries and $b_\kappa,c_\kappa\in L^\infty$. Each $\mathscr B_\kappa$ is a mixed boundary operator, Dirichlet on $\Gamma_0^\kappa$ and $\partial_{\nu_\kappa}w+\beta_\kappa w$ on $\Gamma_1^\kappa$, with $\beta_\kappa$ of **arbitrary sign**. The coefficients $a,b,c,d\in\mathcal C(\bar\Omega)$ satisfy $a,d>0$, $b,c\ge0$, $b\ne0\ne c$, and $\lambda,\mu\in\mathbb{R}$. A **coexistence state** is a solution with both components positive.

Notation:

- $\sigma_0[\mathscr L+V,\mathscr B,\Omega]$ is the principal eigenvalue, and $\sigma_{0,\kappa}=\sigma_0[\mathscr L_\kappa,\mathscr B_\kappa,\Omega]$.
- $\theta_{[\mathscr L,\rho,\xi]}$ is the unique positive solution of the logistic problem $\mathscr Lw=\rho w-\xi w^2$, $\mathscr Bw=0$. It exists iff $\rho>\sigma_0[\mathscr L,\mathscr B,\Omega]$; set it to $0$ otherwise. The semitrivial states are $(\theta_{[\mathscr L_1,\lambda,a]},0)$ and $(0,\theta_{[\mathscr L_2,\mu,d]})$.
- The curves of change of stability of the semitrivial states are

$$
\Phi(\mu)=\sigma_0\bigl[\mathscr L_1+b\,\theta_{[\mathscr L_2,\mu,d]},\mathscr B_1,\Omega\bigr],\qquad \Psi(\lambda)=\sigma_0\bigl[\mathscr L_2-c\,\theta_{[\mathscr L_1,\lambda,a]},\mathscr B_2,\Omega\bigr].
$$

$\Phi$ is increasing in $\mu\ge\sigma_{0,2}$, and $\Psi$ is decreasing in $\lambda\ge\sigma_{0,1}$ with $\Psi(\lambda)\to-\infty$.

**Theorem.**

1. **Existence.** The problem has a coexistence state iff

$$(\lambda,\mu)\in\mathscr R_{\rm coex}=\{\lambda>\sigma_{0,1},\ \lambda>\Phi(\mu),\ \mu>\Psi(\lambda)\},$$

that is, iff both semitrivial states are linearly unstable.
2. **Local uniqueness near $\lambda=\Phi(\mu)$.** For fixed $\mu>\sigma_{0,2}$, an unbounded component of coexistence states, whose $\lambda$-projection is $(\Phi(\mu),\infty)$, bifurcates from $(0,\theta_{[\mathscr L_2,\mu,d]})$ at $\lambda=\Phi(\mu)$. Near the bifurcation point it is an analytic curve $s\mapsto(\lambda(s),u(s),v(s))$ with $\lambda'(0)>0$. Hence there is $\vartheta(\mu)>0$ such that for every $\lambda\in(\Phi(\mu),\Phi(\mu)+\vartheta]$ the coexistence state is unique.
3. **Local uniqueness near $\mu=\Psi(\lambda)$.** Symmetrically, for fixed $\lambda>\sigma_{0,1}$, a component bifurcates from $(\theta_{[\mathscr L_1,\lambda,a]},0)$ at $\mu=\Psi(\lambda)$ with $\mu'(0)>0$. The coexistence state is unique for $\mu\in(\Psi(\lambda),\Psi(\lambda)+\eta(\lambda)]$.

## Expansion

Writing the system as $(\mathscr L_1+au+bv)u=\lambda u$, $(\mathscr L_2+dv-cu)v=\mu v$ and using uniqueness of the principal eigenvalue gives $\lambda>\sigma_{0,1}$ and $\mu>\sigma_{0,2}$. Comparison with the semitrivial states, via monotonicity of $\sigma_0$ in the potential, then gives the necessity of $(\lambda,\mu)\in\mathscr R_{\rm coex}$. Sufficiency follows from Crandall–Rabinowitz local bifurcation and Rabinowitz global bifurcation for the compact analytic perturbation of the identity $\mathscr F$ obtained by inverting $\mathscr L_\kappa+\omega$. Positive invertibility (the strong maximum principle for operators with $\sigma_0>0$) keeps the branches positive. Transversality $\lambda'(0)>0$ and the implicit function theorem give uniqueness in a neighborhood of each bifurcation curve. This is the first uniqueness result valid in every dimension for this non-cooperative system.

## Sources

- J. López-Gómez, E. Muñoz-Hernández, "Uniqueness of coexistence states in diffusive predator-prey models, at the occasion of the 100th anniversary of the first publication of V. Volterra on the predator-prey system", arXiv preprint (2026), Theorem 4.1, with Theorems 3.1–3.3 and Corollary 3.4 (preliminaries), <https://doi.org/10.48550/arXiv.2611.24855>.
