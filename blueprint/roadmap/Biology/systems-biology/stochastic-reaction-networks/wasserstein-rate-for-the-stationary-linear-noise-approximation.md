# Wasserstein rate for the stationary linear noise approximation

**Setting.** A stochastic chemical reaction network with $n$ species, stoichiometry matrix $S$ and volume $\Omega$ is a continuous-time Markov chain $\mathbf X_\Omega(t)$ on $\Omega^{-1}$-scaled lattices, with propensities $\Omega\bar\lambda_i(\mathbf X_\Omega/\Omega)$ for densities $\bar\lambda_i$ that are $C^2$ with bounded derivatives on the state space $\mathcal X\subseteq\mathbb R^n_{\ge0}$, and with stoichiometry spanning $\mathbb R^n$ (the standing assumptions of Section 2). The reaction rate equation is $\dot{\mathbf v}=F(\mathbf v)=S\bar{\boldsymbol\lambda}(\mathbf v)$. At an interior equilibrium $\mathbf v^*$ with Hurwitz Jacobian $J=\partial F(\mathbf v^*)/\partial\mathbf v$, the linear noise approximation (LNA) is the Ornstein–Uhlenbeck process $d\mathbf Y=J\mathbf Y\,dt+S\operatorname{diag}\sqrt{\bar{\boldsymbol\lambda}(\mathbf v^*)}\,d\mathbf W$, whose stationary law is $\mathbf Y^\infty\sim\mathcal N(0,P^\infty)$ with

$$JP^\infty+P^\infty J^{\mathsf T}=-S\operatorname{diag}\big(\bar{\boldsymbol\lambda}(\mathbf v^*)\big)S^{\mathsf T}.$$

Let $\tilde{\mathbf X}^\infty_\Omega=\sqrt\Omega\,(\mathbf X^\infty_\Omega/\Omega-\mathbf v^*)$ be the centered, rescaled stationary state, and $\mathcal W_1$ the 1-Wasserstein distance.

**Theorem 3.1.** Suppose the propensities are bounded by a polynomial of degree $\kappa$, the stationary distribution is unique with finite moment of order $\kappa+1$ for all large $\Omega$, and the first and second stationary moments of $\tilde{\mathbf X}^\infty_\Omega$ are bounded uniformly in $\Omega$. Then there are $C,\Omega_0'$ such that for $\Omega\ge\Omega_0'$

$$\mathcal W_1\big(\tilde{\mathbf X}^\infty_\Omega,\mathbf Y^\infty\big)\le C\,\frac{\ln\Omega}{\sqrt\Omega}.$$

In particular $\tilde{\mathbf X}^\infty_\Omega\Rightarrow\mathcal N(0,P^\infty)$, and $\mathbf X^\infty_\Omega/\Omega\to\mathbf v^*$ in $\mathcal W_1$ at rate $O(\ln\Omega/\Omega)$ (Corollary 3.1).

**Checkable sufficient conditions.**
- (Corollary 3.2) For mass-action networks with only zeroth- and first-order reactions, the bound holds whenever $J$ is Hurwitz.
- (Theorem 3.2) It holds if the reaction rate equation is globally exponentially stable at $\mathbf v^*$, i.e. $\|\mathbf v(t)-\mathbf v^*\|\le Ke^{-\gamma_1t}\|\mathbf v_0-\mathbf v^*\|$ on $\mathcal X$, and some $\mathbf c\in\mathbb R^n_{>0}$ satisfies $\mathbf c^{\mathsf T}F(\mathbf v)\le-\gamma_2\mathbf c^{\mathsf T}\mathbf v$ whenever $\mathbf c^{\mathsf T}\mathbf v\ge d$.

## Expansion

Stein's method compares generators: for a 1-Lipschitz test function $h$, solve the Stein equation $G_{\mathbf Y}f=h-\mathbb E h(\mathbf Y^\infty)$ for the OU generator $G_{\mathbf Y}f(\mathbf x)=\nabla f\cdot J\mathbf x+\tfrac12\sum D_{ij}\partial_{ij}f$. Since $\mathbb E[G_{\tilde{\mathbf X}}f(\tilde{\mathbf X}^\infty_\Omega)]=0$ at stationarity, $\mathbb E h(\tilde{\mathbf X}^\infty_\Omega)-\mathbb E h(\mathbf Y^\infty)=\mathbb E[(G_{\mathbf Y}-G_{\tilde{\mathbf X}})f(\tilde{\mathbf X}^\infty_\Omega)]$, and Taylor-expanding the jump generator shows the difference is $O(\Omega^{-1/2})$ times moments of $\tilde{\mathbf X}^\infty_\Omega$ and derivatives of $f$. Derivative bounds for Stein solutions of diffusions with Wasserstein decay (Gorham et al., Theorem 4.1) control $f$, with a logarithmic loss from smoothing $h$. For linear networks the LNA moments are exact, giving the uniform moment bounds; Theorem 3.2 obtains them from a Lyapunov function built from exponential stability of the ODE.

## Sources

- T. W. Grunberg, D. Del Vecchio, "A Stein's Method Approach to the Linear Noise Approximation for Stationary Distributions of Chemical Reaction Networks", arXiv preprint (2023), Theorem 3.1, Corollaries 3.1–3.2, Theorem 3.2 and Theorem 4.1, <https://doi.org/10.48550/arXiv.2309.07386>.
