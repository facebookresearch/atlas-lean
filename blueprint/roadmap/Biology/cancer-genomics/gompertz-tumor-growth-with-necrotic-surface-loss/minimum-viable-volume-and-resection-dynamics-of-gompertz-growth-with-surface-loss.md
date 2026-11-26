# Minimum viable volume and resection dynamics of Gompertz growth with surface loss

**Setting.** Tumor volume $V(t) \ge 0$ follows a Gompertz law with a necrotic loss proportional to surface area,

$$\frac{dV}{dt} = r_g V \ln\Big(\frac{K}{V}\Big) - \lambda V^{2/3}, \qquad r_g, K, \lambda > 0.$$

A non-trivial equilibrium $V_\infty \in (0,K)$ satisfies $r_g\ln(K/V_\infty) = \lambda V_\infty^{-1/3}$. Surgery at time $t_{op}$ acts by the **resection operator** $\mathcal R(V) = (1-\eta)V + \epsilon$ with efficiency $\eta \in (0,1)$ and minimum residual volume $\epsilon > 0$; afterwards growth resumes with postoperative parameters $(r_p, K_{post})$.

**Theorem.**
1. (Minimum viable volume, Theorem 2.1) Write $\frac{dV}{dt}=V^{2/3}g(V)$ with $g(V)=r_gV^{1/3}\ln(K/V)-\lambda$. Since $g(V)\to-\lambda$ as $V\to0^+$, there is $\delta_0>0$ with $g\le-\lambda/2$ on $(0,\delta_0)$, so $\frac{dV}{dt}\le-\frac\lambda2V^{2/3}$ there, and every solution with $V(0)\in(0,\delta_0)$ reaches $V=0$ by time $6V(0)^{1/3}/\lambda$. Moreover there is $\delta > 0$ such that every solution with $V(0) \in (0,K)$ eventually satisfies $V(t) \le K - \delta$.

   Negative drift alone does not imply extinction. The function $g$ increases on $(0,Ke^{-3})$ and decreases afterwards, with maximum $3r_gK^{1/3}e^{-1}-\lambda$. If $\lambda>3r_gK^{1/3}/e$, then $g<0$ on $(0,\infty)$ and every positive solution reaches $0$ in finite time. If $\lambda<3r_gK^{1/3}/e$, then $g$ has exactly two zeros $V_1<Ke^{-3}<V_\infty<K$; the basin of finite-time extinction is exactly $(0,V_1)$, and every solution with $V(0)>V_1$ converges to $V_\infty$, including those started above $V_\infty$, where the drift is negative. For example, with $K=r_g=1$ and $\lambda=2^{-1/3}\ln2$, $V=1/2$ is an equilibrium and the solution from $V(0)=3/4$ decreases to $1/2$ without reaching $0$.
2. (Convergence rate, Theorems 2.2 and 3.1) $V_\infty$ is locally asymptotically stable when $V_\infty > Ke^{-3}$, with linearized rate

$$\alpha = r_g - \tfrac13\lambda V_\infty^{-1/3} = r_g\Big[1 - \tfrac13\ln\Big(\frac{K}{V_\infty}\Big)\Big].$$

3. (Resection, Theorem 3.2 and Proposition 1) $\mathcal R$ is a contraction with Lipschitz constant $1-\eta$, its unique fixed point is $V^* = \epsilon/\eta$, and $\mathcal R(V) \ge \epsilon$. Surgery reduces the volume if and only if $V(t_{op}^-) > V^*$, i.e. $\eta V(t_{op}^-)/\epsilon > 1$.
4. (Adjuvant kill rate, Proposition 2) Adding a kill term $-\delta V$ keeps $V \le V_{crit}$ in the long run provided $\delta \ge r_p\ln(K_{post}/V_{crit}) - \lambda V_{crit}^{-1/3}$.
5. (Cube-root linearization, Theorem 4.1) For the early postoperative law $\dot V = rV - \kappa V^{2/3}$ with $r \ne 0$, $\kappa > 0$,

$$V(t) = \Big[\Big(V_{res}^{1/3} - \frac{\kappa}{r}\Big)e^{rt/3} + \frac{\kappa}{r}\Big]^3;$$

if $r < 0$ the tumor is cleared at $T_{ext} = \frac{3}{|r|}\ln\big(1 + |r|V_{res}^{1/3}/\kappa\big)$, and if $r > 0$ the volume $(\kappa/r)^3$ is an unstable threshold separating regression from regrowth.
6. (Radiotherapy, Theorem 4.4) For $\dot V = -\Psi(t)D(t)V$ with radiosensitivity $\Psi(t)=\alpha+\beta\sin(2\pi t/\tau)\ge0$ on $[0,T]$ and doses $0 \le D \le D_{max}$, $\int_0^T D \le D_{total}$, every dose schedule minimizing $V(T)$ satisfies, for a constant threshold $\lambda^*$, $D^* = D_{max}$ almost everywhere on $\{\Psi > \lambda^*\}$ and $D^* = 0$ almost everywhere on $\{\Psi < \lambda^*\}$; on $\{\Psi=\lambda^*\}$ the dose is free, subject only to the budget. A bang–bang optimum ($D^*\in\{0,D_{max}\}$ almost everywhere) can always be chosen. Every optimum is bang–bang when $\{\Psi=\lambda^*\}$ is a null set, as for $\beta\ne0$; when $\beta=0$ and $0<D_{total}<TD_{max}$, every schedule spending the whole budget is optimal, the constant schedule $D\equiv D_{total}/T$ included. If $D_{total}\ge TD_{max}$, the optimum is $D^*\equiv D_{max}$.

## Expansion

Near $V = 0$ the loss $\lambda V^{2/3}$ dominates $r_gV\ln(K/V)$, because $V^{1/3}\ln(K/V) \to 0$; on that interval $\dot V \le -cV^{2/3}$, so $\frac{d}{dt}V^{1/3}\le -c/3$ and the volume reaches zero in finite time, unlike the pure Gompertz law where every small tumor grows. Away from zero the sign of $g$ decides the long-time behavior, and since $g'(V)=r_gV^{-2/3}\big[\tfrac13\ln(K/V)-1\big]$ the equilibria are the at most two zeros of $g$, separated by $Ke^{-3}$. Differentiating the equilibrium condition gives $f'(V_\infty) = \frac13\lambda V_\infty^{-1/3} - r_g$, hence the rate formula and the stability condition $\ln(K/V_\infty) < 3$. The substitution $u = V^{1/3}$ turns $\dot V = rV - \kappa V^{2/3}$ into the linear equation $\dot u = \frac r3 u - \frac\kappa3$. The radiotherapy problem is linear in the control: $\ln V(T) = \ln V(0) - \int_0^T \Psi D$, so the problem is to maximize the linear functional $\int_0^T\Psi D$, an optimal schedule spends the dose budget where radiosensitivity is highest, and doses on a level set of $\Psi$ can be exchanged without changing the objective.

## Sources

- Sumit Roy, "A mathematical model to predict growth and treatment for UPS cancer", Bulletin of Mathematical Biology 88 (2026) 122, <https://doi.org/10.1007/s11538-026-01694-4>; preprint arXiv:2512.21620 (2025), Sections 2–4, Theorems 2.1, 2.2, 3.1, 3.2, 4.1 and 4.4, Propositions 1–2, <https://doi.org/10.48550/arXiv.2512.21620>.
