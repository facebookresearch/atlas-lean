# Transition function of a subordinated Wright–Fisher process

**Definition.** Let $X$ be the neutral $K$-type Wright–Fisher diffusion on the simplex $\Delta_K$ with parent-independent mutation parameters $\theta=(\theta_1,\dots,\theta_K)\in(0,\infty)^K$, $|\theta|=\sum_i\theta_i$, generator

$$\mathcal{L}=\tfrac12\sum_{i=1}^K(\theta_i-|\theta|x_i)\,\partial_{x_i}+\tfrac12\sum_{i,j=1}^K x_i(\delta_{ij}-x_j)\,\partial_{x_i}\partial_{x_j},$$

and transition function $p_t(x,du)$. Let $C$ be a non-decreasing Feller process on $[0,\infty]$ with $C(0)=0$, independent of $X$. The *subordinated Wright–Fisher process* is $\widetilde X(t)=X(C(t))$. Two key clock families: a Lévy subordinator $S$ with Laplace exponent $\psi(\lambda)=\beta\lambda+\int_{(0,\infty)}(1-e^{-\lambda s})\pi(ds)$ (Markov, with jumps), and the inverse $R(t)=\inf\{u:S(u)>t\}$ of a subordinator (continuous, non-Markov, with memory).

**Theorem.** Let $\Phi_t(\lambda)=\mathbb{E}[e^{-\lambda C(t)}]$, $\lambda_n=n(n+|\theta|-1)/2$, let $\mathcal{D}_\theta$ be the Dirichlet law, $\mathcal{M}(\mathbf{l};m,x)$ the multinomial probability, and $Q_n(x,u)=\sum_{|\mathbf{n}|=n}Q_{\mathbf{n}}(x)Q_{\mathbf{n}}(u)$ the reproducing kernels of the polynomials orthogonal with respect to $\mathcal{D}_\theta$.

1. $\widetilde X$ is $\mathcal{D}_\theta$-stationary and $\mathcal{D}_\theta$-reversible, and $\widetilde p_t(x,dw)=\mathbb{E}[p_{C(t)}(x,dw)]$.
2. For all $t\ge0$ and $x\in\Delta_K$,
$$\widetilde p_t(x,du)=\sum_{n=0}^\infty\Phi_t(\lambda_n)\,Q_n(x,u)\,\mathcal{D}_\theta(du)
=\sum_{m=0}^\infty\widetilde q_m^{|\theta|}(t)\sum_{|\mathbf{l}|=m}\mathcal{M}(\mathbf{l};m,x)\,\mathcal{D}_{\theta+\mathbf{l}}(du),$$
with
$$\widetilde q_m^{|\theta|}(t)=\sum_{j=m}^\infty(-1)^{j-m}\,\Phi_t(\lambda_j)\,\frac{(2j+|\theta|-1)\,(m+|\theta|)_{(j-1)}}{m!\,(j-m)!}\ \ge0 .$$
So the conditional-expectation operators have eigenvalues $\Phi_t(\lambda_n)$; the leading non-trivial one, $\Phi_t(\lambda_1)$, sets the rate of convergence to $\mathcal{D}_\theta$.
3. For $C=S$, $\Phi_t(\lambda_n)=e^{-t\psi(\lambda_n)}$ (exponential memory). For $C=R$, $t\mapsto\Phi_t(\lambda)$ solves the Volterra equation
$$\Phi_t(\lambda)-1=-\lambda\int_0^t\kappa(t-s)\,\Phi_s(\lambda)\,ds,$$
where $\kappa$ is the potential density of $S$; equivalently $\beta\,\partial_t\Phi_t+\int_0^t\partial_s\Phi_s\,\bar\pi(t-s)\,ds=-\lambda\Phi_t$ with $\bar\pi(s)=\pi((s,\infty))$. For the inverse of an $\alpha$-stable subordinator, $\Phi_t(\lambda)=E_\alpha(-\lambda t^\alpha)$ is a Mittag-Leffler function, giving heavy-tailed memory; for $K=2$ this is a (shifted) fractional Jacobi diffusion.

## Depends on

- [Line-of-descent mixture representation of the Wright–Fisher transition function](../diffusion-theory/transition-densities-of-wright-fisher-diffusions/line-of-descent-mixture-representation-of-the-tr.md)

## Expansion

Conditioning on the independent clock gives $\widetilde p_t=\mathbb{E}[p_{C(t)}]$. The Wright–Fisher transition function has the spectral expansion $\sum_ne^{-\lambda_nt}Q_n\mathcal{D}_\theta$ and the line-of-descent expansion with the death-process probabilities $q_m(t)=\sum_{j\ge m}(-1)^{j-m}e^{-\lambda_jt}a_{jm}$. Replacing $t$ by $C(t)$ and taking expectations (Fubini, justified by smoothness) replaces each $e^{-\lambda_nt}$ by $\Phi_t(\lambda_n)$; stationarity and reversibility are inherited because they hold for every fixed time. Positivity of $\widetilde q_m$ follows since it is an average of probabilities. For an inverse subordinator, $\Phi_t$ satisfies the renewal-type equation obtained from the first-passage structure $\{R(t)>u\}=\{S(u)<t\}$.

## Sources

- N. A. Judd, D. Spanò, "Subordinated Wright-Fisher Priors", arXiv:2604.11363 (2026), Definition 1, Propositions 1–3 and Section 3.3. <https://doi.org/10.48550/arXiv.2604.11363>
