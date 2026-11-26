# Equilibria and tumor-free threshold of the delayed tumor–effector model

**Model.** Let $T(t)\ge 0$ and $E(t)\ge 0$ be the concentrations of tumor and effector cells. For delays $\tau_1,\tau_2\ge 0$ consider

$$
\begin{aligned}
\dot T(t) &= T(t)\,f(t,T(t)) - \gamma E(t)T(t),\\
\dot E(t) &= \sigma + \frac{p\,E(t)\,T(t-\tau_1)}{g + a\,T(t-\tau_1)} - \frac{m\,E(t)\,T(t-\tau_2)}{g + a\,T(t-\tau_2)} - \eta E(t),
\end{aligned}
$$

with $\gamma,\sigma,\eta,p,m,g>0$, $a\ge 0$, and Richards-type relative growth $f(t,T)=r\big[(1-T^{\beta})/\beta - b(t)\big]$, where $r>0$, $0<\beta\le 1$ and $b$ is continuous and periodic (chemotherapy). Here $\tau_1$ is the immune response delay and $\tau_2$ the delay of effector neutralization. For constant $b\equiv\hat b<1/\beta$ the autonomous growth law is (after $r\to r/\beta$) $f(T)=r(b-T^{\beta})$ with $b:=1-\beta\hat b>0$.

**Statements.**

1. *(Positivity.)* Every solution with a continuous nonnegative initial history on $[-\max(\tau_1,\tau_2),0]$ is defined for all $t\ge 0$ and stays nonnegative.
2. *(No closed orbits without delay.)* If $\tau_1=\tau_2=0$ and $b$ is constant, the system has no nontrivial nonnegative periodic solutions.
3. *(Tumor-free threshold.)* The tumor-free equilibrium $(0,\sigma/\eta)$ always exists. With $\Delta := \gamma\sigma - r b\eta$, for **all** $\tau_1,\tau_2\ge 0$: it is unstable if $\Delta<0$, locally stable if $\Delta=0$, and locally asymptotically stable if $\Delta>0$.
4. *(Positive equilibria.)* After the scaling $\sigma\to\sigma\gamma/(\eta r)$, $m\to m/(\eta g)$, $p\to p/(\eta g)$, $a\to a/g$ and $\mu:=m-p$, every equilibrium other than the tumor-free one satisfies $0<T\le b^{1/\beta}$, $E=f(T)/\gamma$ and $S(T,\mu,a)=b-\sigma$, where

$$
S(T,\mu,a) = T\Big[(a+\mu)T^{\beta} + T^{\beta-1} - \big(b(\mu+a) - a\sigma\big)\Big].
$$

5. *(Uniqueness for $a=0$.)* Let $\beta,b\in(0,1)$, $a=0$ and $\mu_c := \Big(\tfrac1b\big(\tfrac{1-\beta}{1+\beta}\big)^{\beta-1}\Big)^{1/\beta}$. If either $\sigma<b$ and $\mu\le 0$, or $\sigma\le b$ and $0<\mu\le\mu_c$, then there is exactly one positive equilibrium $(T_*,E_*)$, where $T_*\in(0,b^{1/\beta}]$ is the simple root of $\mu(T^{\beta}-b)T + T^{\beta} = b-\sigma$ and $E_* = r(b-T_*^{\beta})/\gamma$. If instead $b\le\sigma$ and $\mu\le\mu_c$, the tumor-free point is the only admissible equilibrium.
6. *(Stability of the tumor-present state.)* For $a,\tau_1,\tau_2\ge 0$ small and $\sigma<b$, $\mu\le 0$, the equilibrium $(T_{*,a},E_{*,a})$ continued from $(T_*,E_*)$ is locally asymptotically stable.

## Expansion

At $(0,\sigma/\eta)$ the delayed terms enter the linearization only through entries that multiply $T$, so the characteristic function factors as $(\lambda+\eta)\big(\lambda - rb + \gamma\sigma/\eta\big)$ and contains no exponential: the delays cannot destabilize the tumor-free state, and the threshold is the sign of $\Delta$. In scaled units $\Delta>0$ is $\sigma>b$, the complement of the hypothesis in item 5, so the tumor-free and tumor-present states trade stability at $\sigma=b$. At a general equilibrium the characteristic function is $P(\lambda) + \gamma h'(\hat T)\hat T\hat E\,(p e^{-\tau_1\lambda} - m e^{-\tau_2\lambda})$ with $h(s)=s/(g+as)$; for $\tau_1=\tau_2=0$ and $\mu\le 0$ its trace is negative and its determinant positive, and continuity in $(a,\tau_1,\tau_2)$ gives item 6. Item 2 follows from Dulac's criterion with weight $1/(TE)$, whose weighted divergence is $-\big(r\beta T^{\beta-1} + \sigma/(TE)\big)/E<0$. Item 5 reduces to monotonicity and convexity properties of $T\mapsto \mu(T^{\beta}-b)T+T^{\beta}$ on $[0,b^{1/\beta}]$; for larger $\mu$ up to three positive equilibria can coexist.

## Sources

- P. Amster, A. Rivera, J. A. Arredondo, *Periodic solutions in a tumor-immune competition system with time-delay and chemotherapy effects*, arXiv:2510.11135 (2025). <https://doi.org/10.48550/arXiv.2510.11135> — Theorem 5 (positivity), Lemma 6 (Dulac), Section 3 (equilibrium equation), Propositions 7–9 (equilibrium counts for $a=0$), Theorem 10 (tumor-free threshold), Theorem 12 (local stability).
