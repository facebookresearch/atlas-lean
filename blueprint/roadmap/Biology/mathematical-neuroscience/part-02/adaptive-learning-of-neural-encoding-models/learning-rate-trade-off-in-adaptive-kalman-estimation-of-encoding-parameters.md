# Learning-rate trade-off in adaptive Kalman estimation of encoding parameters

**Model.** A continuous neural feature $y_t$ (e.g. a local field potential power) is encoded linearly in a known brain-state regressor $\tilde v_t \in \mathbb{R}^n$:

$$y_t = \psi'\tilde v_t + z_t, \qquad z_t \sim \mathcal{N}(0, Z),$$

with unknown fixed parameter $\psi^* \in \mathbb{R}^n$. Adaptive estimation treats $\psi$ as a random walk $\psi_t = \psi_{t-1} + s_t$, $s_t \sim \mathcal{N}(0, sI_n)$, and runs the Kalman filter

$$\Sigma_{t|t-1} = \Sigma_{t-1|t-1} + sI_n, \quad \Sigma_{t|t}^{-1} = \Sigma_{t|t-1}^{-1} + \tilde v_t \tilde v_t' Z^{-1}, \quad \psi_{t|t} = \psi_{t-1|t-1} + \Sigma_{t|t}\tilde v_t Z^{-1}(y_t - \tilde v_t'\psi_{t-1|t-1}).$$

The variance $s > 0$ is the **learning rate**: it sets how strongly new observations override the current estimate.

**Theorem (error and convergence as functions of $s$).** Assume $\tilde v_t$ is periodic with period $T$, let $H = \frac{1}{T}\sum_{t=1}^{T}\tilde v_t\tilde v_t' Z^{-1} = U\,\mathrm{diag}(h_1, \dots, h_n)\,U'$ with $0 < h_1 \le \dots \le h_n$, and set

$$\kappa_m = \frac{\sqrt{h_m^2 s^2 + 4h_m s} - h_m s}{2h_m}.$$

Then, in the approximation of the analysis, the steady-state covariance of the error $g_t = \psi^* - \psi_{t|t}$ is

$$\Sigma^*_\infty = U\,\mathrm{diag}\Big(\frac{1}{\sqrt{h_m^2 + 4h_m/s}}\Big)_{m}\,U',$$

each eigenvalue increasing in $s$, and the mean error contracts as

$$\mathbb{E}[g_t] = U\,\mathrm{diag}\Big(\frac{\kappa_m}{\kappa_m + s}\Big)_m U'\,\mathbb{E}[g_{t-1}], \qquad \frac{\kappa_m}{\kappa_m + s} = 1 - \frac{\sqrt{h_m^2 s^2 + 4h_m s} - h_m s}{2},$$

each factor decreasing in $s$; the slowest mode $m = 1$ governs convergence.

**Calibration.** (i) The largest learning rate with $\|\Sigma^*_\infty\|_2 \le V$ is

$$s = \frac{4h_1}{V^{-2} - h_1^2}, \qquad \text{valid when } V^{-2} > h_1^2 .$$

(ii) To reach relative error $E$ within time $C$ at sampling interval $\Delta$, choose the smallest $s$ with $\big(\kappa_1/(\kappa_1 + s)\big)^{C/\Delta} \le E$, which has a closed-form solution.

## Expansion

With a constant information rate $H$ in place of $\tilde v_t \tilde v_t' Z^{-1}$, the covariance recursion becomes the scalar Riccati recursion $\sigma \mapsto \big((\sigma + s)^{-1} + h\big)^{-1}$ in each eigendirection of $H$. Its prior-variance form has the fixed point solving $h\kappa^2 + hs\kappa - s = 0$, whose positive root is $\kappa_m$, and the posterior variance at the fixed point is $(\kappa_m^2 + s\kappa_m)/(2\kappa_m + s) = 1/\sqrt{h_m^2 + 4h_m/s}$. The Kalman gain at this fixed point gives the mean-error contraction factor $\kappa_m/(\kappa_m + s)$. A larger $s$ means less averaging: faster tracking of parameter changes, larger steady-state jitter. The same analysis extends to point-process filters for spiking encoding models, where the information matrix is replaced by its expected Fisher-information counterpart. In use, $V$ or $C$ is set from performance requirements and only the average of $\tilde v_t\tilde v_t'$ over training trajectories is needed.

## Sources

- H. Hsieh, M. M. Shanechi, "Optimizing the learning rate for adaptive estimation of neural encoding models", PLoS Computational Biology 14 (2018) e1006168, Methods (encoding model (1), random-walk prior (2), Kalman recursions (3)–(6), Theorem 1 with equations (7)–(8), Theorem 2 with equation (9)), <https://doi.org/10.1371/journal.pcbi.1006168>.
