# Perron-weighted decay of networked SIQR epidemics under spectral isolation constraints

**Model.** Consider $n$ regions with susceptible, asymptomatic, symptomatic and isolated proportions $s_i, x_i^{a}, x_i^{s}, k_i$, a nonnegative infection-flow matrix $A = [a_{ij}]$, transmission rates $\beta = (\beta^{a}, \beta^{s}) \in \mathbb{R}_{>0}^2$ bounded by $\beta_{\max}$, symptom onset rate $\epsilon > 0$, recovery rates $r^{a}, r^{s}, r^{q} > 0$ and isolation controls $q_i^{a}, q_i^{s} \in [0, B]$:

$$
\begin{aligned}
\dot s_i &= -s_i \sum_{j=1}^{n} a_{ij}\big(\beta^{a} x_j^{a} + \beta^{s} x_j^{s}\big), &
\dot x_i^{a} &= -\dot s_i - (\epsilon + r^{a} + q_i^{a})\,x_i^{a},\\
\dot x_i^{s} &= \epsilon x_i^{a} - (r^{s} + q_i^{s})\,x_i^{s}, &
\dot k_i &= q_i^{a} x_i^{a} + q_i^{s} x_i^{s} - r^{q} k_i.
\end{aligned}
$$

The infected state $y = (x^{a}, x^{s}) \in \mathbb{R}_{\ge 0}^{2n}$ satisfies $\dot y = M(s, q \mid \beta)\,y$ with

$$
M(s, q \mid \beta) = \begin{pmatrix} \beta^{a}\operatorname{diag}(s)A - (\epsilon + r^{a})I_n - \operatorname{diag}(q^{a}) & \beta^{s}\operatorname{diag}(s)A \\ \epsilon I_n & -\big(r^{s} I_n + \operatorname{diag}(q^{s})\big) \end{pmatrix}.
$$

$M$ is Metzler and entrywise nondecreasing in $s$ and $\beta$; since $\dot s \le 0$, it is nonincreasing in time for fixed $q$ and $\beta$. Let $\lambda_{\max}(\cdot)$ denote the spectral abscissa.

**Proposition (decay under per-step spectral constraints).** Let the control and transmission be constant, $q = q_m$, $\beta = \beta_m$, on sampling intervals $[t_m, t_{m+1})$; let the graph of $A$ be strongly connected and $s_i(t) > 0$ on $[t_0, T]$, with $t_{M_{\mathrm{tot}}} \le T < t_{M_{\mathrm{tot}}+1}$. Put $M_m = M(s(t_m), q_m \mid \beta_m)$ and suppose $\lambda_{\max}(M_m) \le -\alpha < 0$ for $m = 0, \dots, M_{\mathrm{tot}}$. If $v_m > 0$ is the left Perron eigenvector of $M_m$ with $\|v_m\|_1 = 1$, then

$$
v_m^\top y(t) \le e^{-\alpha(t - t_m)}\,v_m^\top y(t_m), \qquad t \in [t_m, t_{m+1}),
$$

and $\|y(t)\|_1 \le C_T\, e^{-\alpha(t - t_0)}\|y(t_0)\|_1$ on $[t_0, T]$ with $C_T = (\bar v_T/\underline v_T)^{M_{\mathrm{tot}}+1}$, where $\bar v_T$ and $\underline v_T$ are the largest and smallest entries of the $v_m$.

**Invariance of the terminal set.** With maximal isolation $q_{\mathrm{safe}} = (B, \dots, B)$, the set $\mathcal{X}_f = \{x : \lambda_{\max}(M(s(x), q_{\mathrm{safe}} \mid \beta_{\max})) \le -\alpha\}$ is positively invariant under $q_{\mathrm{safe}}$ for every $\beta \le \beta_{\max}$ (for any integration scheme that keeps $s$ nonincreasing). Consequently, once a trajectory reaches $\mathcal{X}_f$ at time $t^*$, applying $q_{\mathrm{safe}}$ forever gives $\|y(t)\|_1 \le C_\infty e^{-\alpha(t - t^*)}\|y(t^*)\|_1$ for all $t \ge t^*$, with $C_\infty$ the ratio of the largest to smallest entry of the Perron vector at $t^*$. **MPC guarantees.** Consider a model predictive controller enforcing $\lambda_{\max}(M_m) \le -\alpha$ stage-wise and $\mathcal{X}_f$ as terminal constraint, and assume (the source's Assumption 4) that its prediction model is exact and its transmission forecast matches the true $\beta$ over the horizon. Then (Theorem 1) feasibility at $t_m$ implies feasibility at $t_{m+1}$; (Theorem 2) if the problem is feasible at $t_0$, the closed loop satisfies, for every $T > t_0$, $\|y(t)\|_1 \le C_T e^{-\alpha(t-t_0)}\|y(t_0)\|_1$ on $[t_0,T]$ with the horizon-dependent $C_T$ above; and (Theorem 3) there is an admissible control, namely the optimal sequence computed at $t_0$ followed by $q_{\mathrm{safe}}$ from $t_0 + H\Delta t$ on, and a time-independent $C > 0$ with $\|y(t)\|_1 \le Ce^{-\alpha(t-t_0)}\|y(t_0)\|_1$ for all $t \ge t_0$. Global decay is thus proved for this continuation, not for the receding-horizon loop.

## Expansion

On $[t_m, t_{m+1})$ susceptibles only decrease, so $M(s(t), q_m \mid \beta_m) \le M_m$ entrywise. With $V_m = v_m^\top y$ and $y \ge 0$, $\dot V_m = v_m^\top M(s(t), q_m\mid\beta_m) y \le v_m^\top M_m y = \lambda_{\max}(M_m) V_m \le -\alpha V_m$, and Grönwall gives the per-interval contraction. Switching Perron vectors at sampling instants costs a factor $\bar v_T/\underline v_T$ each time, hence $C_T$, which may grow with the horizon. Invariance of $\mathcal{X}_f$ uses monotonicity of the spectral abscissa of Metzler matrices: as $s$ decreases the matrix decreases and so does $\lambda_{\max}$. After the switch to $q_{\mathrm{safe}}$ a single Perron vector serves for all later times, which removes the horizon dependence. Depletion of susceptibles, not a quadratic Lyapunov function, drives the invariance.

## Sources

- Mahtab Talaei, Alexander Olshevsky, Laura F. White, Ioannis Ch. Paschalidis, "Network Epidemic Control via Model Predictive Control", IEEE Control Systems Letters 10 (2026), 1597–1602, <https://doi.org/10.1109/lcsys.2026.3707462>. Published version of arXiv:2604.13357, cited next; locators there refer to the arXiv version.
- Mahtab Talaei, Alex Olshevsky, Laura F. White, Ioannis Ch. Paschalidis, *Network Epidemic Control via Model Predictive Control: Extended Version*, arXiv 2026. Section 2 (networked SIQR model, Proposition 1, Lemma 1), Theorem 1 (recursive feasibility), Theorem 2 and Theorem 3 (finite-horizon and global exponential decay). <https://doi.org/10.48550/arXiv.2604.13357>
