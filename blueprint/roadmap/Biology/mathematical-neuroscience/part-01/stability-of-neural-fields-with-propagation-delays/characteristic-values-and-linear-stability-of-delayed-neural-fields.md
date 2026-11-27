# Characteristic values and linear stability of delayed neural fields

**Model.** On an open bounded set $\Omega \subset \mathbb R^d$, $p$ neural populations have membrane potentials $V(r,t) \in \mathbb R^p$ obeying

$$\partial_t V(r,t) = -L_0V(r,t) + \int_\Omega J(r,\bar r)\,S\big(V(\bar r, t - \tau(r,\bar r))\big)\,d\bar r + I^{\mathrm{ext}}(r,t),$$

where $L_0 = \operatorname{diag}(l_1,\dots,l_p)$ with $l_i > 0$, $S(x) = (S(\sigma_i(x_i - h_i)))_i$ with a sigmoid $S:\mathbb R\to(0,1)$, $J \in L^2(\Omega^2,\mathbb R^{p\times p})$, and the delay matrix $\tau$ is continuous with maximum $\tau_m$ (e.g. $\tau_{ij}(r,\bar r) = c\,\|r - \bar r\|$). The phase space is $C([-\tau_m,0], L^2(\Omega,\mathbb R^p))$. Delayed and undelayed equations share the same stationary (persistent) states $V_f$. Linearizing at $V_f$ gives $\dot U = -L_0U + \int_\Omega J(r,\bar r)DS(V_f(\bar r))\,U(\bar r, t-\tau(r,\bar r))\,d\bar r$, with generator $\mathcal A$ and solution semigroup $(T(t))_{t\ge0}$.

**Characteristic values.** For $\lambda\in\mathbb C$ let $J(\lambda)U(r) = \int_\Omega J(r,\bar r)DS(V_f(\bar r))e^{-\lambda\tau(r,\bar r)}U(\bar r)\,d\bar r$, a compact operator on $L^2$, and $\Delta(\lambda) = \lambda\,\mathrm{Id} + L_0 - J(\lambda)$. The characteristic values are the $\lambda$ for which $\Delta(\lambda)$ is not injective.

**Theorem.**
1. $\Sigma_{\mathrm{ess}}(\mathcal A) = \Sigma(-L_0) = \{-l_1,\dots,-l_p\}$.
2. $\Sigma(\mathcal A)$ is at most countable and equals $\Sigma(-L_0)$ together with the characteristic values; each characteristic value outside $\Sigma(-L_0)$ is an isolated eigenvalue with finite-dimensional generalized eigenspace.
3. Only finitely many characteristic values satisfy $\Re\lambda > -\min_i l_i$.
4. $(T(t))$ is norm continuous for $t > \tau_m$, and $0$ is asymptotically stable for the linearized equation if and only if $\max\Re\,\Sigma_p(\mathcal A) < 0$; in that case the persistent state $V_f$ is asymptotically stable for the nonlinear equation.

## Proof depends on

- [Essential Spectrum add compact](../../../../Analysis/not-yet-classified/essential-spectrum/essential-spectrum-add-compact.md)

## Expansion

The spectrum of $\mathcal A$ is linked to that of the family $L_\lambda = -L_0 + J(\lambda)$ on the Hilbert space $L^2$: $\lambda \in \Sigma_{\mathrm{ess}}(\mathcal A)$ iff $\lambda \in \Sigma_{\mathrm{ess}}(L_\lambda)$, and the essential spectrum is invariant under the compact perturbation $J(\lambda)$, giving part 1. Analytic Fredholm theory then makes the remaining spectrum discrete, and for $\Re\lambda$ large $\|(\lambda+L_0)^{-1}J(\lambda)\| < 1$, which confines characteristic values with $\Re\lambda > -\min l_i$ to a bounded set. Because the generator is neither sectorial nor of pure point spectrum, the step from spectrum to semigroup decay uses eventual norm continuity: for such semigroups the growth bound equals the spectral bound, and the spectral bound is a maximum by part 3. Linear stability passes to the nonlinear equation by a variation-of-constants estimate inside the bounded absorbing set of trajectories.

## Sources

- R. Veltz, O. Faugeras, "Stability of the stationary solutions of neural field equations with propagation delays", Journal of Mathematical Neuroscience 1 (2011) 1, Section 2 (model, Eq (1)), Definition 3.2, Lemma 3.3, Proposition 3.4, Corollaries 3.5, 3.7 and 3.8 and Lemma 3.6, <https://doi.org/10.1186/2190-8567-1-1>, PMCID PMC3280889.
