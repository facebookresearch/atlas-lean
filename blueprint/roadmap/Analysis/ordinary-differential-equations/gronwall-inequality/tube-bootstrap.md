# Tube bootstrap for perturbed trajectories

Let $E$ be a real normed space, $v : \mathbb{R} \times E \to E$ a time-dependent vector field, $K \ge 0$, and $\varepsilon, \delta, T, r$ real numbers with $T \ge 0$, $\varepsilon \ge 0$ and $r > 0$. Let $f, g, g' : \mathbb{R} \to E$ and suppose that

- for every $t \in [0, T]$, $v(t, \cdot)$ is $K$-Lipschitz on the closed ball $\bar B(f(t), r)$;
- $f$ is continuous on $[0, T]$ and has right derivative $f'(t) = v(t, f(t))$ for $t \in [0, T)$;
- $g$ is continuous on $[0, T]$, and for $t \in [0, T)$ with $g(t) \in \bar B(f(t), r)$, $g$ has right derivative $g'(t)$ with $\|g'(t) - v(t, g(t))\| \le \varepsilon$;
- $\|f(0) - g(0)\| \le \delta$;
- $G(T) < r$, where $G(t) = \delta e^{Kt} + \frac{\varepsilon}{K}(e^{Kt} - 1)$ for $K > 0$ and $G(t) = \delta + \varepsilon t$ for $K = 0$ is the Gronwall bound.

Then for every $t \in [0, T]$, $g(t)$ stays in the tube $\bar B(f(t), r)$ and $\|f(t) - g(t)\| \le G(t)$.
