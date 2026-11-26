# Extended Kalman filter error bounds for bilinear compartmental epidemic models

**Setting.** Consider a compartmental model whose drift has only linear and bilinear (mass-action) terms and whose outputs are linear in the state,

$$\dot x = A x + \sum_{(i,j)\in\mathcal{B}} b_{ij}\,x_i x_j + B u, \qquad y = C x,$$

with $\mathcal{B}$ a finite set of couplings. It is discretised by Euler's method with step $T$, $x_{k+1} = \varphi(x_k) + w_k$, $y_k = C x_k + v_k$, with independent zero-mean Gaussian noises of covariances $Q_d$ and $R$, and an extended Kalman filter (EKF) linearises $\varphi$ at the current estimate with Jacobian $F_k$.

**Theorem (Reif–Günther–Yaz–Unbehauen, specialised).** Suppose (A1) the EKF covariance stays in a window $\underline{p}\,I \preceq P_k \preceq \overline{p}\,I$ (guaranteed by uniform observability and uniform controllability of the noise input), (A2) $F_k$ and $C$ are bounded, and (A3) the linearisation remainders satisfy quadratic bounds. Then there are $\epsilon^\ast, \delta^\ast > 0$, $0 < \vartheta < 1$ and $\nu > 0$ such that, whenever $\|x_0 - \hat x_{0|-1}\| \le \epsilon^\ast$ and $\mathrm{tr}(Q_d), \mathrm{tr}(R) \le \delta^\ast$, the prediction error $\xi_k = x_k - \hat x_{k|k-1}$ obeys

$$\mathbb{E}\|\xi_k\|^2 \le \vartheta^k\,\frac{\overline{p}}{\underline{p}}\,\mathbb{E}\|\xi_0\|^2 + \frac{\nu}{1 - \vartheta}.$$

**Proposition (bilinear structure makes (A3) automatic).** For $g(x_i,x_j) = x_i x_j/N$ the first-order Taylor remainder is exactly $(x_i - \hat x_i)(x_j - \hat x_j)/N$. Hence for bilinear-drift, linear-output systems the remainder of $\varphi$ is a finite sum of such rank-one terms, the quadratic bound holds globally ($\epsilon_\varphi = \infty$) with an explicit constant determined by $|\mathcal{B}|$ and the coefficients, and the measurement remainder vanishes. EKF mean-square boundedness then reduces to uniform observability along the trajectory.

**Example (nine-compartment COVID-19 model).** For a model with states $S, E, V, I_1, I_2, P, H, R, F$ (two infectious strains, a vaccinated class and a protected class), inputs $\beta(t), w_1(t)$ and outputs $y = (H, F, V)$, the observability matrix of Lie derivatives of orders $0$–$2$ has

$$\det \mathcal{O}_9 = \pm\,\delta_w\,\gamma_a^2\,\kappa\,\rho_2\,w_1^2\,(\delta_i - \delta_p)^2\,(r_1 - r_2),$$

so it is singular only on the parameter set $\delta_i = \delta_p$ or $r_1 = r_2$; there a third Lie level restores full rank, and the system is locally observable wherever $S, V > 0$, $\beta, w_1 > 0$, $r_2 > 0$ and at least one of $I_1, I_2, P$ is positive. Observability is lost at the disease-free equilibrium, where no epidemic signal reaches the outputs.

## Expansion

The general EKF theorem combines a stochastic Lyapunov function $\xi^\top P_k^{-1}\xi$ with bounds on the nonlinear remainder; its weakest hypotheses in practice are the remainder bounds, which usually hold only in a small neighbourhood. Mass-action incidence removes that difficulty, because its Taylor series stops at second order. What remains model-specific is a lower bound on the observability Gramian along the trajectory, checked through the Lie-derivative rank; the determinant formula shows exactly which parameter coincidences (equal death rates or equal recovery rates across strains) make two infectious classes indistinguishable from hospitalisations, deaths and vaccinations alone. The constant $\vartheta$ sets how fast the filter forgets its initial guess, and $\nu/(1-\vartheta)$ is the noise floor of the estimate.

## Sources

- Lokman Rachid Melhani, Antonino Sferlazza, Dominique Persano Adorno, Filippo D'Ippolito, Antonino Lo Burgio, Alberto Firenze, "Extended Kalman Filter-Based State Estimation for a Nine-Compartment Nonlinear Epidemic Model -- Convergence Analysis", arXiv:2606.16305 (2026), Lemma 1, Remark 3, Proposition 1, Theorem 1 (statement of the Reif–Günther–Yaz–Unbehauen theorem), Lemma 2, Remarks 8–9, Lemma 3 and Theorem 2, <https://doi.org/10.48550/arXiv.2606.16305>.
