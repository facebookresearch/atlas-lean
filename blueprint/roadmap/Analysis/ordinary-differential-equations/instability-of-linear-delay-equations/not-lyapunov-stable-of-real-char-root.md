# A positive real characteristic root destabilizes a delay equation

Let $F$ be a real normed space, $\tau \ge 0$, and $\mathcal{C} = C([-\tau, 0], F)$. Let $\Lambda : \mathcal{C} \to F$ be continuous linear, defining the delay equation $x'(t) = \Lambda(x_t)$, and let $L : \mathcal{C} \to \mathcal{C}$ be a continuous linear time-$T$ solution map of it, $T > 0$. Let $\Phi : \mathbb{R} \times \mathcal{C} \to \mathcal{C}$ and $u_0 \in \mathcal{C}$, and let $\rho > 0$, $C \ge 0$, $p > 1$, $M$, $\mu$ and $r > 0$ satisfy:

- $\Phi(0, x) = x$, and $\Phi((n+1)T, x) = \Phi(T, \Phi(nT, x))$ whenever $\|\Phi(kT, x) - u_0\| \le \rho$ for all $k \le n$;
- $\|\Phi(T, u_0 + y) - u_0 - L y\| \le C \|y\|^p$ for $\|y\| \le \rho$;
- there is $v \ne 0$ in $F$ with $\Lambda(\theta \mapsto e^{\theta r} v) = r v$ (a real characteristic root $r$);
- $0 \le \mu < e^{p T r}$ and $\|L^n\| \le M \mu^n$ for all $n$.

Then $u_0$ is not Lyapunov stable for $\Phi$.
