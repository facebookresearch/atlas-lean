# Exact probability-flow solution for Gaussian data

Setting (variance-exploding, as in Wang and Vastola, who follow the EDM formulation): data
$X_0 \sim \mathcal{N}(\mu, \Sigma)$ in $\mathbb{R}^D$ with $\Sigma$ real symmetric positive
semidefinite, possibly singular, and the continuous densities $p(\cdot\,; \sigma)$ of the laws of
$X_0 + \sigma \varepsilon$ with $\varepsilon \sim \mathcal{N}(0, I)$ independent of $X_0$. Let
$J$ be a closed bounded interval and let $t \mapsto \sigma_t$ be continuously differentiable on
$J$ with $\sigma_t > 0$ for every $t \in J$, endpoints included; $\sigma$ need not be monotone.
Write $C_t = \Sigma + \sigma_t^2 I$, which is positive definite. With the score of the
Gaussian marginal (first page under Informally uses),
$\nabla \log p(x; \sigma_t) = -C_t^{-1} (x - \mu)$, the probability-flow ODE
$\dot{x} = -\dot{\sigma}_t \sigma_t \nabla \log p(x; \sigma_t)$ becomes the linear system

$$\dot{x}(t) = A(t) \bigl(x(t) - \mu\bigr), \qquad A(t) = \dot{\sigma}_t \sigma_t C_t^{-1}.$$

$A$ is continuous on $J$, and the matrices $A(t)$, being functions of $\Sigma$, commute with one
another.

Statement: for all $s, t \in J$ and $x \in \mathbb{R}^D$, the unique solution on $J$ with
$x(s) = x$ takes at time $t$ the value

$$X_{s,t}(x) = \mu + C_t^{1/2} C_s^{-1/2} (x - \mu),$$

with positive definite square roots. In a real orthonormal eigenbasis $u_1, \dots, u_D$ of
$\Sigma$, with $\Sigma u_k = \lambda_k u_k$ and $\lambda_k \ge 0$, zero eigenvalues included,

$$X_{s,t}(x) = \mu + \sum_{k=1}^{D} \psi_k(s, t) \langle u_k, x - \mu \rangle u_k,
\qquad \psi_k(s, t) = \sqrt{\frac{\lambda_k + \sigma_t^2}{\lambda_k + \sigma_s^2}},$$

and a direction with $\lambda_k = 0$ has the factor $\sigma_t / \sigma_s$. The formula covers both
orientations, $t < s$ and $t > s$; when $\sigma$ increases with $t$, sampling runs from $s$ down
to $t < s$, as in Wang and Vastola's backward integration from a large noise level. With Wang and Vastola's initial level $\sigma_T$ in
the role of $\sigma_s$, it is their closed-form solution.

Proof: in the eigenbasis, $c_k(t) = \langle u_k, x(t) - \mu \rangle$ satisfies
$\dot{c}_k = \frac{\dot{\sigma}_t \sigma_t}{\lambda_k + \sigma_t^2} c_k
= \tfrac{1}{2} \frac{d}{dt} \log(\lambda_k + \sigma_t^2) \, c_k$, so
$c_k(t) = \psi_k(s, t) c_k(s)$; equivalently, $\frac{d}{dt} C_t^{1/2} = \tfrac{1}{2} \dot{C}_t
C_t^{-1/2}$ because the $C_t$ commute, which shows directly that $X_{s,t}(x)$ solves the system.
Uniqueness: extend $A$ continuously from $J$ to $\mathbb{R}$, for instance by the constant values
$A(a)$ before the left endpoint $a$ and $A(b)$ after the right endpoint $b$. A solution on $J$
continues, by solving the extended system from $a$ and from $b$, to a solution of the extended
system on $\mathbb{R}$; the one-sided derivatives agree at $a$ and $b$ because $A$ is continuous.
The fundamental-matrix theorem, applied to $x - \mu$, gives uniqueness on $\mathbb{R}$, hence
on $J$.

Singular covariance: if $\Sigma$ is singular, the noise level $0$ is only a limit. In a direction
with $\lambda_k = 0$ the coefficient is $\dot{\sigma}_t / \sigma_t$, which is not integrable as
$\sigma_t \to 0^+$, so $\sigma = 0$ is outside the domain of the system and the uniqueness
argument does not apply there. As $\sigma_t \to 0^+$ with $s$ fixed, $X_{s,t}(x)$ converges to
$\mu + \sum_{\lambda_k > 0} \sqrt{\lambda_k / (\lambda_k + \sigma_s^2)}
\langle u_k, x - \mu \rangle u_k$, Wang and Vastola's noise-to-sample map. This limit map has
rank $\operatorname{rank} \Sigma$, so it is not invertible when $\Sigma$ is singular, and it
carries $\mathcal{N}(\mu, \Sigma + \sigma_s^2 I)$ to the degenerate $\mathcal{N}(\mu, \Sigma)$.
Solutions starting at noise level $0$ are not unique: for $\sigma_t = t$ the equation
$\dot{c} = c / t$ of a $\lambda_k = 0$ direction has the solutions $c(t) = K t$ for every $K$,
all with limit $0$ at $t = 0$. If $\Sigma$ is positive definite, $A$ stays continuous where
$\sigma_t = 0$, and such an endpoint is regular.

Affine noising paths (derived): let $X_t = \alpha_t X_0 + \sigma_t \varepsilon$ with $\alpha$ and
$\sigma$ continuously differentiable on $J$, and suppose
$C_t = \alpha_t^2 \Sigma + \sigma_t^2 I$ is positive definite for every $t \in J$, as it is when
$\sigma_t > 0$ on $J$. The variance-exploding setting above is $\alpha \equiv 1$; a
variance-preserving schedule has $\alpha_t^2 + \sigma_t^2 = 1$. The marginal velocity
$v(z, t) = \mathbb{E}[\dot{\alpha}_t X_0 + \dot{\sigma}_t \varepsilon \mid X_t = z]$ is
$v(z, t) = \dot{\alpha}_t \mu + \tfrac{1}{2} \dot{C}_t C_t^{-1} (z - \alpha_t \mu)$, and the flow
of $\dot{z} = v(z, t)$ is
$X_{s,t}(z) = \alpha_t \mu + C_t^{1/2} C_s^{-1/2} (z - \alpha_s \mu)$, with spectral factors
$\sqrt{(\alpha_t^2 \lambda_k + \sigma_t^2) / (\alpha_s^2 \lambda_k + \sigma_s^2)}$. For a
variance-preserving schedule with $\alpha_t > 0$, $v$ is the Gaussian-score probability-flow ODE of Wang and
Vastola's appendix on the VP formulation, and for $\alpha > 0$ the flow is their scaled solution,
which they obtain by substituting $x_t \mapsto x_t / \alpha_t$ and $\sigma_t \mapsto
\sigma_t / \alpha_t$. The formula here also covers a time where $\alpha_t = 0$, the pure-noise end
of a path such as $\alpha_t = 1 - t$, $\sigma_t = t$ at $t = 1$, where that substitution is
undefined.

Further properties (derived), for $s, t, \tau \in J$ in the variance-exploding setting:

- (i) Composition: $C_\tau^{1/2} C_t^{-1/2} C_t^{1/2} C_s^{-1/2} = C_\tau^{1/2} C_s^{-1/2}$,
  so $X_{t,\tau} \circ X_{s,t} = X_{s,\tau}$ and $X_{t,s}$ is the inverse of $X_{s,t}$; in the
  eigenbasis, $\psi_k(t, \tau) \psi_k(s, t) = \psi_k(s, \tau)$. This illustrates the composition
  property of flow maps in the indexing of Boffi, Albergo and Vanden-Eijnden, where $X_{s,t}$
  sends the state at time $s$ to the state at time $t$; their framework is stated for
  interpolant time in $[0, 1]$, and the Gaussian example here is derived, not taken from their paper.
- (ii) Transport of marginals: with $\Phi = C_t^{1/2} C_s^{-1/2}$, which is symmetric,
  $\Phi C_s \Phi^{\mathsf{T}} = C_t$, so $X_{s,t}$ carries $\mathcal{N}(\mu, C_s)$ to
  $\mathcal{N}(\mu, C_t)$: centre at $\mu$, apply the linear map $\Phi$, and translate back.
- (iii) Volume: $\det \partial X_{s,t} = \det \Phi = \prod_{k=1}^{D} \psi_k(s, t)
  = \exp \int_s^t \operatorname{tr} A(r) \, dr$, with the oriented integral, consistent with
  Liouville's formula for the fundamental matrix of the system.

## Informally uses

- [Score and optimal denoiser for Gaussian data](gaussian-data-score-and-denoiser.md):
  mathematical prerequisite, the score $-C_t^{-1} (x - \mu)$ that defines the probability-flow
  ODE.
- [Fundamental matrix of a linear system](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/fundamental-matrix-linear-system.md):
  mathematical prerequisite, uniqueness of the solution, applied after the coefficient is extended
  continuously from $J$ to $\mathbb{R}$, since that theorem asks for a coefficient continuous on
  all of $\mathbb{R}$; it does not reach the noise level $0$ when $\Sigma$ is singular.

## Background

- [Linear images of multivariate Gaussians](../../../Probability/distributions/continuous/gaussian-conditioning/map-to-euclidean-lin-multivariate-gaussi.md):
  background, the linear step of (ii).

## Sources

- B. Wang and J. J. Vastola, "The Unreasonable Effectiveness of Gaussian Score Approximation for Diffusion Models and its Applications", arXiv:2412.09726 (version 1), Section 2.1, equation (2) and its footnote 1 (the probability-flow ODE, with $\sigma_t = t$ not assumed); Section 3.2, equations (14) and (15) (the linear system and its solution), equation (17) (the noise-to-sample map), and the paragraph "Solution with data scaling term" with equation (18) (the substitution and the scaled solution); Appendix D.1, equations (44)–(54) (derivation; setting $\lambda_k = 0$ recovers the component orthogonal to the data subspace); Appendix D.3, equation (69) ($\alpha_t^2 + \sigma_t^2 = 1$) and equations (70)–(71) (the variance-preserving probability-flow ODE).
- N. M. Boffi, M. S. Albergo and E. Vanden-Eijnden, "Flow map matching with stochastic interpolants: A mathematical framework for consistency models", arXiv:2406.07507 (version 2), Section 3, Definition 3.4, equation (3.6) (the indexing $X_{s,t}(x_s) = x_t$), and Proposition 3.5, equation (3.8) (the composition property, for times in $[0, 1]$).
- AI-authored exposition.
