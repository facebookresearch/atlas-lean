# Threshold for extinction of the leukaemic stem cell population

**Model.** This is a reduced PDE version of the Roeder–Loeffler agent-based model of haematopoiesis in chronic myeloid leukaemia. $A(t)$ is the number of quiescent, fully immature stem cells, and $\Omega(x,t)$ is the density of proliferating cells at maturity level $x \in [0,1]$; cells lose stemness as $x$ increases. Proliferating cells mature at speed $\rho_d > 0$, divide at net rate $b > 0$ and return to quiescence at rate $\alpha(x, A)$. Quiescent cells activate at rate $\omega(\Omega_{\rm tot})$, where $\Omega_{\rm tot}(t) = \int_0^1\Omega(x,t)\,dx$:

$$\frac{dA}{dt} = -\omega(\Omega_{\rm tot})A + \int_0^1\alpha(x,A)\,\Omega(x,t)\,dx,\qquad \partial_t\Omega + \rho_d\,\partial_x\Omega = \big(b - \alpha(x,A)\big)\Omega,$$

$$\Omega(0,t) = \frac{\omega(\Omega_{\rm tot})}{\rho_d}A(t).$$

The feedback functions $\alpha$ and $\omega$ are continuous, positive, bounded and decrease to zero.

**Threshold quantity.** Define

$$\mathcal{R} = \frac{1}{\rho_d}\int_0^1 \alpha(x,0)\exp\Big(\frac{1}{\rho_d}\int_0^x\big(b - \alpha(s,0)\big)\,ds\Big)dx .$$

It acts as a reproduction number for the cycle quiescence → activation → maturation → return to quiescence, with the feedbacks at their zero-population values: the paper's conditions read $\mathcal{R} > 1$, $\mathcal{R} < 1$ and $\mathcal{R} \le 1$.

**Theorem.**

1. *(Steady states)* Zero is always a steady state, and a nonzero steady state exists, and is unique, if and only if $\mathcal{R} > 1$.
2. *(Linearization)* For constant positive $\alpha(x)$ and $\omega$, the linearized eigenvalue problem has a unique real eigenvalue $\lambda$ with positive eigenvector. It solves $\rho_d(\lambda/\omega + 1) = \int_0^1\alpha(x)e^{\frac{1}{\rho_d}\int_0^x(b-\alpha(s)-\lambda)ds}dx$, and $\lambda > 0$ if and only if $\mathcal{R} > 1$.
3. *(Extinction)* If $\alpha(x, A)$ is positive and decreasing in $A$ and $\mathcal{R} \le 1$, the zero steady state is globally attractive. If $\mathcal{R} > 1$ it is unstable.

Thus the zero state is stable exactly when it is the only steady state. For $x$-independent $\alpha$, the condition $\mathcal{R} > 1$ reduces to $\alpha(0) > b^*$, where $b^*$ is the second root of $b e^{-b/\rho_d} = b^* e^{-b^*/\rho_d}$ (with $b^* = \rho_d$ when $b = \rho_d$).

## Expansion

Along characteristics, $\Omega(x) = \Omega(0)\exp\big(\frac{1}{\rho_d}\int_0^x(b - \alpha - \lambda)\big)$. Substituting into the boundary and quiescent equations gives $G(\lambda) = L(\lambda)$, where $G$ increases linearly from $-\infty$ to $+\infty$ and $L$ decreases from $+\infty$ to $0$. This yields a unique crossing, which is positive exactly when $G(0) < L(0)$. Global attractivity uses the general relative entropy method: test the solution against the positive adjoint eigenfunction $\phi$, set $v(t) = \int\phi\,\Omega\,dx + \phi(0)A$, and use the monotonicity of $\alpha$ in $A$ to show that $v$ is nonincreasing and drives the population to zero. When $\alpha$ is independent of $x$, the method of characteristics turns the PDE into a delay system with delay $1/\rho_d$. Its characteristic equation coincides with the eigenvalue relation, which links the model to Mackey-type delay models of CML.

## Sources

- M. Doumic-Jauffret, P. S. Kim and B. Perthame, "Stability Analysis of a Simplified Yet Complete Model for Chronic Myelegenous Leukemia", arXiv:0909.0637 (2009), Section 3 (Approximations 3 and 4) and Propositions 5.1, 5.2, 5.3 and 5.5, <https://doi.org/10.48550/arXiv.0909.0637>.
