# Global stability of the degree-based SIR model with distributed infectivity delay

**Setting.** Consider the degree-based SIR model with distributed infectivity delay on an uncorrelated network,

$$\dot S_k = \mu - \mu S_k - \beta k S_k \int_0^\infty f(\tau) e^{-(\mu+\gamma)\tau}\, \theta(t-\tau)\, d\tau, \qquad \dot I_k = \beta k S_k \int_0^\infty f(\tau) e^{-(\mu+\gamma)\tau}\, \theta(t-\tau)\, d\tau - (\mu + \gamma) I_k,$$

$k = 1, \dots, n$, with $\theta(t) = \sum_k a_k I_k(t)$, $a_k = kP(k)/\langle k\rangle$, $\mu, \beta, \gamma > 0$, an integrable kernel $f \ge 0$, $\hat f = \int_0^\infty f(\tau) e^{-(\mu+\gamma)\tau}\, d\tau > 0$, and $\mathcal R_0 = \beta \hat f \langle k^2\rangle / ((\mu+\gamma)\langle k\rangle)$. Initial data are continuous with positive histories, $I_k(u) = \phi_k(u) > 0$ for $u \le 0$ (source Eq. (4)); the set $\Omega = \{0 \le S_k, I_k,\ S_k + I_k \le 1\}$ is positively invariant.

**Theorem.**

1. If $\mathcal R_0 \le 1$, the disease-free equilibrium $E_0$ ($S_k = 1$, $I_k = 0$) is the only equilibrium and is globally asymptotically stable in $\Omega$.
2. If $\mathcal R_0 > 1$, the unique endemic equilibrium $E_+ = (S_k^*, I_k^*)_k$ is globally asymptotically stable for solutions in $\Omega$ with such positive histories.

So the delay kernel changes the value of the threshold through $\hat f$ but cannot create oscillations or multistability: the dynamics are those of a sharp threshold at $\mathcal R_0 = 1$.

## Depends on

- [Threshold of the degree-based SIR model with distributed infectivity delay](threshold-of-the-degree-based-sir-model-with-distributed-infectivity-delay.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

*Item 1.* Take

$$V = \sum_k a_k \int_1^{S_k} \frac{x - 1}{x}\, dx + \sum_k a_k I_k + \frac{\mu+\gamma}{\hat f} \int_0^\infty f(\tau) e^{-(\mu+\gamma)\tau} \int_{t-\tau}^{t} \theta(v)\, dv\, d\tau .$$

Along solutions the $S_k$ factors in the incidence cancel and $\sum_k a_k (\mu+\gamma) I_k = (\mu+\gamma)\theta(t)$, which gives

$$\dot V = -\mu \sum_k a_k \frac{(S_k - 1)^2}{S_k} + \frac{\mu + \gamma}{\hat f}\, (\mathcal R_0 - 1) \int_0^\infty f(\tau) e^{-(\mu+\gamma)\tau}\, \theta(t-\tau)\, d\tau \le 0,$$

and LaSalle's invariance principle gives convergence to $E_0$.

*Item 2.* For each $k$ use the Volterra-type functional

$$V_k = S_k - S_k^* - S_k^* \ln\frac{S_k}{S_k^*} + I_k - I_k^* - I_k^* \ln\frac{I_k}{I_k^*} + \beta k S_k^* \sum_j a_j I_j^* \int_0^\infty \alpha(\tau)\, \psi\Bigl(\frac{I_j(t-\tau)}{I_j^*}\Bigr) d\tau,$$

with $\psi(x) = x - 1 - \ln x \ge 0$ and $\alpha(\tau) = \int_\tau^\infty f(s) e^{-(\mu+\gamma)s}\, ds$. Integration by parts in the delay term turns $\dot V_k$ into $-\mu(S_k - S_k^*)^2/S_k$ plus a sum over arcs $j \to k$ of nonpositive terms of the form $-\psi(\cdot)$ and a cyclic remainder $G_{kj} = \bigl(I_j/I_j^* - \ln(I_j/I_j^*)\bigr) - \bigl(I_k/I_k^* - \ln(I_k/I_k^*)\bigr)$. Weight $V = \sum_k c_k V_k$ with $c_k > 0$ the diagonal cofactors of the Laplacian of the weighted digraph with arc weights $\bar\beta_{kj} = \beta k \hat f S_k^* a_j I_j^*$, which is strongly connected because all weights are positive. By Kirchhoff's matrix-tree theorem $\sum_{k,j} c_k \bar\beta_{kj} G_{kj} = 0$, so $\dot V \le 0$, with equality only at $E_+$, and LaSalle's principle finishes the proof.

## Sources

- C. Huang, J. Cao, F. Wen, X. Yang, "Stability Analysis of SIR Model with Distributed Delay on Complex Networks", *PLoS ONE* 11(8) (2016) e0158813, Lemma 1, Theorems 3–4, Lemma 2 and Eqs. (17)–(25). <https://doi.org/10.1371/journal.pone.0158813> (PMC4973911).
- M. Y. Li, Z. Shuai, "Global-stability problem for coupled systems of differential equations on networks", *Journal of Differential Equations* 248 (2010) 1–20. <https://doi.org/10.1016/j.jde.2009.09.003>.
