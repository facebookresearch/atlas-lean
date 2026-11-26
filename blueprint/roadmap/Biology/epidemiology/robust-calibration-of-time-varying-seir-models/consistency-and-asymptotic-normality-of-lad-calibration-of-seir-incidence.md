# Consistency and asymptotic normality of LAD calibration of SEIR incidence

**Model.** In a closed population of size $N$, with latent rate $\sigma > 0$, removal rate $\gamma > 0$ and a transmission rate $\beta(t;\theta) \ge 0$ indexed by a finite-dimensional parameter $\theta \in \mathcal{H}$,

$$\dot S = -\beta(t;\theta)\frac{S I}{N}, \quad \dot E = \beta(t;\theta)\frac{S I}{N} - \sigma E, \quad \dot I = \sigma E - \gamma I, \quad \dot R = \gamma I, \quad \dot C = \sigma E,\ C(0) = 0.$$

Observations are reporting-interval incidences $Y_j = \mu_j(\theta_0) + \varepsilon_{Tj}$, $j = 1, \dots, T$, with

$$\mu_j(\theta) = C(\tau_j;\theta) - C(\tau_{j-1};\theta) = \int_{\tau_{j-1}}^{\tau_j}\sigma E(u;\theta)\, du.$$

The **LAD calibration** $\hat\theta_T$ minimizes $\bar L_T(\theta) = T^{-1}\sum_{j=1}^T |Y_j - \mu_j(\theta)|$; let $Q_T = \mathbb{E}\,\bar L_T$.

**Theorem.**

1. *(Well-posedness.)* If $x(0) = (S,E,I,R)(0) \in \Delta_N = \{x \in \mathbb{R}_+^4 : \mathbf{1}^{\mathsf T}x = N\}$ and $t \mapsto \beta(t;\theta)$ is continuous and nonnegative on the analysis horizon, the system has a unique solution on the whole horizon, $x(t) \in \Delta_N$ throughout, and $C$ is nondecreasing and finite.
2. *(Parameter differentiability.)* If the vector field and the initial-condition map are $C^1$ in $\theta$ near the compact feasible set, then $x(t;\theta)$, $C(t;\theta)$ and every $\mu_j(\theta)$ are $C^1$ in $\theta$, uniformly on the horizon, with derivatives given by the sensitivity equations.
3. *(Existence and consistency.)* If each $\mu_j$ is continuous on compact $\mathcal{H}$, LAD and least-squares minimizers exist. If moreover the $\mu_j$ are uniformly bounded and uniformly Lipschitz in $\theta$ and the errors are independent with median zero and bounded second moments, then $\sup_{\mathcal{H}}|\bar L_T - Q_T| \to 0$ in probability; under the uniform separation condition $\liminf_T \inf_{\|\theta - \theta_0\| \ge \epsilon}\{Q_T(\theta) - Q_T(\theta_0)\} > 0$, every measurable LAD minimizer is consistent, $\hat\theta_T \to \theta_0$ in probability.
4. *(Asymptotic normality.)* Let $J_{Tj} = \partial_\theta\mu_j(\theta_0)$ and $A_T = T^{-1}\sum_j J_{Tj}J_{Tj}^{\mathsf T}$. Suppose in addition that $\theta_0$ is interior, the errors are i.i.d. with median zero and a density $f$ continuous and positive at $0$, $A_T \to A$ positive definite, $\max_j\|J_{Tj}\|/\sqrt{T} \to 0$, the outputs have a uniform local quadratic remainder and a Lindeberg condition holds. Then

$$\sqrt{T}\,(\hat\theta_T - \theta_0) \xrightarrow{d} N\Big(0,\ \frac{1}{4 f(0)^2}A^{-1}\Big).$$

## Depends on

- [Solution of the closed SEIR system for times t ≥ 0](../seir-epidemic-model/is-solution.md)

## Expansion

The SEIR vector field is locally Lipschitz and preserves the nonnegative simplex (each compartment's outflow vanishes when it is zero, and the total is conserved), so solutions are global on any finite horizon; smooth dependence on parameters is the classical differentiability theorem for ODEs, and integrating $\sigma E$ transfers it to the interval incidences. Consistency follows from a uniform law of large numbers for Lipschitz-indexed averages of $|Y_j - \mu_j(\theta)|$ plus identifiable separation, the standard argmin argument. For normality, the LAD criterion is convex in the residual, and Knight's identity gives the local quadratic approximation $\bar L_T(\theta_0 + u/\sqrt{T}) - \bar L_T(\theta_0) \approx -u^{\mathsf T}W_T/\sqrt T + f(0)\,u^{\mathsf T}A_T u / T$ with $W_T \Rightarrow N(0, A)$; minimizing yields the sandwich covariance $(2f(0))^{-2}A^{-1}$, the same form as median regression. The heavier the error density at zero, the more LAD gains over least squares under reporting spikes.

## Sources

- Yisa Abolade, Yichuan Zhao, Gerardo Chowell, "Calibration of Time-Varying SEIR Models", arXiv (2026). Section "Large-sample theory for LAD calibration": theorems on finite-horizon global well-posedness, parameter differentiability, existence/uniform convergence/consistency, and asymptotic normality of LAD, with the uniform-regularity, uniform-separation and local asymptotic assumptions. <https://doi.org/10.48550/arXiv.2609.23089>
