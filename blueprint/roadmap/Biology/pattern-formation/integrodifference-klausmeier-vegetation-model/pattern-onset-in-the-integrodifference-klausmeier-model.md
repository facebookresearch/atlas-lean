# Pattern onset in the integrodifference Klausmeier model

**Setting.** Consider the [integrodifference Klausmeier model](integrodifference-klausmeier-model-and-consistency.md) at the vegetated steady state $(\bar u, \bar w) = (\bar u_2, \bar w_2)$, and let $\alpha = f_u, \beta = f_w, \gamma = g_u, \delta = g_w$ be the partial derivatives of the growth maps at $(\bar u, \bar w)$.

**Proposition (dispersion relation).** Linearizing and taking Fourier transforms, a perturbation proportional to $\lambda^n e^{ikx}$ exists iff $\lambda$ is an eigenvalue of

$$J(k) = \begin{pmatrix} C\hat\phi(k)\,\alpha & C\hat\phi(k)\,\beta\\ D\hat\phi_1(k)\,\gamma & D\hat\phi_1(k)\,\delta\end{pmatrix},$$

and the steady state is stable to spatially heterogeneous perturbations if $|\lambda(k)| < 1$ for both eigenvalues and all $k > 0$.

**Proposition (Jury criterion).** On flat ground (symmetric $\phi_1$), under the consistency scalings $C = D = T$, $\sigma_\phi^2 = 2T$, second moment of $\phi_1$ equal to $2dT$, and with Laplace kernels $\phi(x) = \frac a2 e^{-a|x|}$ (so $\hat\phi(k) = a^2/(a^2+k^2)$), the steady state is unstable to heterogeneous perturbations if

$$1 + \det J(k) - |\operatorname{tr} J(k)| < 0 \quad\text{for some } k > 0 .$$

**Theorem (onset independent of season length).** In the same setting the steady state is unstable to heterogeneous perturbations whenever $d > d_c(A,B)$, where $d_c(A,B)$ is exactly the diffusion threshold for Turing instability of the vegetated state in the local Klausmeier PDE; in particular the threshold does not depend on $T$. The analysis requires the steady-state structure of the PDE to persist (desert and vegetated state stable to homogeneous perturbations, the middle state unstable), which under $C = D = T$ holds for $T < 1/2$, $B < 2$ and rainfall below an explicit bound $A_+(B,T)$ that becomes unrestricted as $T \to 0^+$.

So this integrodifference formulation cannot express an effect of the temporal separation of dispersal from growth on the onset of patterns; numerical simulations with non-Laplacian kernels are needed for that question.

## Depends on

- [Integrodifference Klausmeier model and its consistency with the PDE model](integrodifference-klausmeier-model-and-consistency.md)
- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Proof depends on

- [Integrodifference Klausmeier model and its consistency with the PDE model](integrodifference-klausmeier-model-and-consistency.md)
- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

Convolution becomes multiplication under the Fourier transform, so the linearized map acts on each wavenumber by the matrix $J(k)$; with symmetric kernels $\hat\phi, \hat\phi_1$ are real and the Jury conditions for a real $2\times2$ matrix ($|\det J| < 1$, $1 - \operatorname{tr} J + \det J > 0$, $1 + \operatorname{tr} J + \det J > 0$) characterize $|\lambda| < 1$; violating the last two gives the displayed instability condition. With Laplace kernels, $\hat\phi$ is rational in $k^2$, so $1 + \det J - |\operatorname{tr} J|$ becomes a rational function of $k^2$ whose sign change is a polynomial condition. Under the scalings ($a^2 = 1/T$ for $\phi$, and the corresponding width for $\phi_1$) the factors of $T$ cancel and the condition reduces to the PDE's Turing condition, which together with consistency as $T \to 0^+$ explains why the threshold coincides with the local model's.

## Sources

- L. Eigentler and J. A. Sherratt, "An integrodifference model for vegetation patterns in semi-arid environments with seasonality", Journal of Mathematical Biology (2020), Section 3, Propositions 2, 4, 5 and 6, Corollary 3 and their proofs, <https://doi.org/10.1007/s00285-020-01530-w> (PMC7519009).
