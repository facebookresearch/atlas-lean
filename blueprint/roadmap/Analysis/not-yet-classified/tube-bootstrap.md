# Tube bootstrap for perturbed trajectories

Let $E$ be a real normed space, $v : \mathbb{R} \times E \to E$ a time-dependent field, $f, g, g' : \mathbb{R} \to E$, $K \ge 0$, and $\varepsilon, \delta, m, T \in \mathbb{R}$ with $T \ge 0$, $\varepsilon \ge 0$ and $m > 0$. Write $\overline{B}(f(t), m)$ for the closed ball of radius $m$ about $f(t)$ and
$$\beta(x) = \begin{cases} \delta e^{Kx} + \dfrac{\varepsilon}{K}\big(e^{Kx} - 1\big), & K \ne 0,\\ \delta + \varepsilon x, & K = 0 \end{cases}$$
for the Gronwall bound. Assume:

- $\beta(T) < m$;
- for every $t \in [0, T]$, $v(t, \cdot)$ is $K$-Lipschitz on $\overline{B}(f(t), m)$;
- $f$ and $g$ are continuous on $[0, T]$;
- for every $t \in [0, T)$, $f$ has right derivative $v(t, f(t))$ at $t$ (derivative within $[t, \infty)$);
- for every $t \in [0, T)$ with $g(t) \in \overline{B}(f(t), m)$, $g$ has derivative $g'(t)$ at $t$ within $[t, \infty)$ and $\|g'(t) - v(t, g(t))\| \le \varepsilon$;
- $\|f(0) - g(0)\| \le \delta$.

Then for every $t \in [0, T]$,
$$g(t) \in \overline{B}(f(t), m) \quad\text{and}\quad \|f(t) - g(t)\| \le \beta(t).$$
