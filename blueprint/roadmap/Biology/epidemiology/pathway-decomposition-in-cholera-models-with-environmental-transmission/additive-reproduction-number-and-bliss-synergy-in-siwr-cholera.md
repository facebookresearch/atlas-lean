# Additive reproduction number and Bliss synergy of sanitation in an SIWR cholera model

**Model.** Susceptible, infected and recovered humans $S, I, R$ (with $N = S + I + R$) and the pathogen concentration $W$ in a shared water reservoir satisfy

$$ \begin{aligned} \dot S &= \Lambda - \beta_1(1-\epsilon_h)\frac{IS}{N} - \beta_2(W)(1-\epsilon_w)S - (\mu+\nu)S, \qquad \dot R = \gamma I + \nu S - \mu R,\\ \dot I &= \beta_1(1-\epsilon_h)\frac{IS}{N} + \beta_2(W)(1-\epsilon_w)S - A I, \qquad \dot W = \theta I - \sigma W, \end{aligned} $$

with $A = \gamma + \mu + \delta$, Monod dose response $\beta_2(W) = \beta_{\max}W/(k+W)$, human-sanitation efficacy $\epsilon_h \in [0,1]$, environmental-sanitation efficacy $\epsilon_w \in [0,1]$ and vaccination rate $\nu \ge 0$; all other parameters are positive. The disease-free equilibrium has $S^\star = \Lambda/(\mu+\nu)$.

**Additive reproduction number.** The next-generation matrix of the $(I, W)$ subsystem is upper triangular, and

$$ \mathcal R_0 = \mathcal R_0^{(h)} + \mathcal R_0^{(e)}, \qquad \mathcal R_0^{(h)} = \frac{\beta_1(1-\epsilon_h)}{A}\cdot\frac{\mu}{\mu+\nu}, \qquad \mathcal R_0^{(e)} = \frac{(1-\epsilon_w)\beta_{\max}\theta}{k\sigma A}\cdot\frac{\Lambda}{\mu+\nu}. $$

With pathway weights $p_h = \mathcal R_0^{(h)}/\mathcal R_0$, $p_e = \mathcal R_0^{(e)}/\mathcal R_0$, the elasticities $\Upsilon_q = \partial\log\mathcal R_0/\partial\log q$ are $\Upsilon_{\beta_1} = p_h$, $\Upsilon_{\beta_{\max}} = \Upsilon_\theta = \Upsilon_\Lambda = p_e$, $\Upsilon_k = \Upsilon_\sigma = -p_e$, $\Upsilon_\gamma = -\gamma/A$, $\Upsilon_\delta = -\delta/A$, $\Upsilon_\nu = -\nu/(\mu+\nu)$.

**Proposition (exact Bliss excess).** For a control leaving a fraction $r_i$ of a burden $Y$, Bliss independence predicts the fraction $\prod_i r_i$ under combined control; the Bliss excess is the predicted remaining fraction minus the observed one. Taking $Y = \mathcal R_0$ and pathway weights evaluated without control, human and environmental sanitation are synergistic with

$$ \mathcal E_{\mathcal R_0}(\epsilon_h, \epsilon_w, \nu) = p_h p_e\, \epsilon_h \epsilon_w\cdot\frac{\mu}{\mu+\nu}, $$

while vaccination is exactly Bliss-independent of both sanitation measures. The factor $p_hp_e\epsilon_h\epsilon_w$ is maximal at $p_h = p_e = \tfrac12$, is at most $\tfrac14\epsilon_h\epsilon_w$, and vanishes iff one route is absent or one efficacy is zero.

**Threshold dynamics.** The disease-free equilibrium is locally asymptotically stable iff $\mathcal R_0 < 1$; it is globally asymptotically stable whenever $\widetilde{\mathcal R}_0 = \beta_1(1-\epsilon_h)/A + \mathcal R_0^{(e)} \le 1$ (equal to $\mathcal R_0$ when $\nu = 0$), a threshold that cannot be improved with Lyapunov functions linear in $(I, W)$. At $\mathcal R_0 = 1$ the system undergoes a forward transcritical bifurcation: for $\mathcal R_0 > 1$ there is a unique endemic equilibrium, locally stable just above threshold, and there is no backward bifurcation.

## Expansion

The remaining fraction of the uncontrolled $\mathcal R_0$ under joint control is $r = (1 - p_h\epsilon_h - p_e\epsilon_w)\frac{\mu}{\mu+\nu}$, while single controls leave $r_h = 1 - p_h\epsilon_h$, $r_w = 1 - p_e\epsilon_w$ and $r_\nu = \mu/(\mu+\nu)$; then $r_hr_wr_\nu - r = p_hp_e\epsilon_h\epsilon_w\,\mu/(\mu+\nu)$. Because $\mathcal R_0$ is a sum over routes, blocking one route leaves the other intact (no environmental sanitation can push $\mathcal R_0$ below $\mathcal R_0^{(h)}$), whereas the multiplicative Bliss null credits each control with a proportional cut of the whole; partial control of both routes beats it by exactly the cross term. Vaccination scales both routes through the susceptible fraction and so factors out. Global stability uses $V = I + cW$ together with $\beta_2(W) \le \beta_{\max}W/k$ and $S \le S^\star$ on an absorbing set, followed by LaSalle's invariance principle; strict concavity of the Monod function also fixes the sign of the centre-manifold coefficient that rules out backward bifurcation.

## Sources

- Abdallah Alsammani, Gassan A. M. O. Farah, Mohammed A. Y. Mohammed, Mehmet Yavuz, "Threshold Dynamics and Integrated Control of Cholera Transmission with Sanitation and Vaccination", arXiv:2505.08873 (2025), Section 2.1 (model, Definition 2.1), Section 3.2 (additive $\mathcal R_0$, Proposition 3.1), Sections 3.3–3.5 (Theorems 3.3, 3.4, 3.7, Proposition 3.5), Section 3.6 (Proposition 3.9). <https://doi.org/10.48550/arXiv.2505.08873>
