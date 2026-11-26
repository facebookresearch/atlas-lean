# Minimum viable volume and resection dynamics of Gompertz growth with surface loss

**Setting.** Tumor volume $V(t) \ge 0$ follows a Gompertz law with a necrotic loss proportional to surface area,

$$\frac{dV}{dt} = r_g V \ln\Big(\frac{K}{V}\Big) - \lambda V^{2/3}, \qquad r_g, K, \lambda > 0.$$

A non-trivial equilibrium $V_\infty \in (0,K)$ satisfies $r_g\ln(K/V_\infty) = \lambda V_\infty^{-1/3}$. Surgery at time $t_{op}$ acts by the **resection operator** $\mathcal R(V) = (1-\eta)V + \epsilon$ with efficiency $\eta \in (0,1)$ and minimum residual volume $\epsilon > 0$; afterwards growth resumes with postoperative parameters $(r_p, K_{post})$.

**Theorem.**
1. (Minimum viable volume, Theorem 2.1) If the trajectory enters the region $r_gV\ln(K/V) < \lambda V^{2/3}$, it reaches $V = 0$ in finite time. Moreover there is $\delta > 0$ such that every solution with $V(0) \in (0,K)$ eventually satisfies $V(t) \le K - \delta$.
2. (Convergence rate, Theorems 2.2 and 3.1) $V_\infty$ is locally asymptotically stable when $V_\infty > Ke^{-3}$, with linearized rate

$$\alpha = r_g - \tfrac13\lambda V_\infty^{-1/3} = r_g\Big[1 - \tfrac13\ln\Big(\frac{K}{V_\infty}\Big)\Big].$$

3. (Resection, Theorem 3.2 and Proposition 1) $\mathcal R$ is a contraction with Lipschitz constant $1-\eta$, its unique fixed point is $V^* = \epsilon/\eta$, and $\mathcal R(V) \ge \epsilon$. Surgery reduces the volume if and only if $V(t_{op}^-) > V^*$, i.e. $\eta V(t_{op}^-)/\epsilon > 1$.
4. (Adjuvant kill rate, Proposition 2) Adding a kill term $-\delta V$ keeps $V \le V_{crit}$ in the long run provided $\delta \ge r_p\ln(K_{post}/V_{crit}) - \lambda V_{crit}^{-1/3}$.
5. (Cube-root linearization, Theorem 4.1) For the early postoperative law $\dot V = rV - \kappa V^{2/3}$ with $r \ne 0$, $\kappa > 0$,

$$V(t) = \Big[\Big(V_{res}^{1/3} - \frac{\kappa}{r}\Big)e^{rt/3} + \frac{\kappa}{r}\Big]^3;$$

if $r < 0$ the tumor is cleared at $T_{ext} = \frac{3}{|r|}\ln\big(1 + |r|V_{res}^{1/3}/\kappa\big)$, and if $r > 0$ the volume $(\kappa/r)^3$ is an unstable threshold separating regression from regrowth.
6. (Radiotherapy, Theorem 4.4) For $\dot V = -\Psi(t)D(t)V$ with radiosensitivity $\Psi \ge 0$ and doses $0 \le D \le D_{max}$, $\int_0^T D \le D_{total}$, every dose schedule minimizing $V(T)$ is bang–bang: $D^* = D_{max}$ where $\Psi > \lambda^*$ and $D^* = 0$ where $\Psi < \lambda^*$ for a constant threshold $\lambda^*$.

## Expansion

Near $V = 0$ the loss $\lambda V^{2/3}$ dominates $r_gV\ln(K/V)$, because $V^{1/3}\ln(K/V) \to 0$; once loss exceeds growth the ratio keeps decreasing, and $\dot V \le -cV^{2/3}$ forces extinction in finite time, unlike the pure Gompertz law where every small tumor grows. Differentiating the equilibrium condition gives $f'(V_\infty) = \frac13\lambda V_\infty^{-1/3} - r_g$, hence the rate formula and the stability condition $\ln(K/V_\infty) < 3$. The substitution $u = V^{1/3}$ turns $\dot V = rV - \kappa V^{2/3}$ into the linear equation $\dot u = \frac r3 u - \frac\kappa3$. The radiotherapy problem is linear in the control: $\ln V(T) = \ln V(0) - \int_0^T \Psi D$, so the optimal schedule spends the dose budget where radiosensitivity is highest.

## Sources

- Sumit Roy, "A mathematical model to predict growth and treatment for UPS cancer", arXiv:2512.21620 (2025), Sections 2–4, Theorems 2.1, 2.2, 3.1, 3.2, 4.1 and 4.4, Propositions 1–2, <https://doi.org/10.48550/arXiv.2512.21620>.
