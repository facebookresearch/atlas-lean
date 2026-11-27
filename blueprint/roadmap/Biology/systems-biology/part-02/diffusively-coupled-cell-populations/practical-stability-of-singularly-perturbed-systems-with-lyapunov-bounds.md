# Practical stability of singularly perturbed systems from slow and boundary-layer Lyapunov functions

Consider a two-time-scale system

$$
\dot x = f(x, z), \qquad \varepsilon \dot z = g(x, z, \varepsilon),
$$

with $x \in D_x \subset \mathbb{R}^n$ ($D_x$ convex), $z \in D_z \subset \mathbb{R}^m$, small $\varepsilon > 0$, $f, g$ continuously differentiable and solutions existing for all $t \ge 0$. Assume:

1. **Quasi-steady state.** There is a $C^1$ map $h : D_x \to D_z$ with $g(x, h(x), 0) = 0$ and $\|\partial h/\partial x\| \le c_1$, and $(0, h(0))$ is an equilibrium at $\varepsilon = 0$.
2. **Stable slow model.** There is $V_S$ with $d_1\|x\|^2 \le V_S(x) \le d_2 \|x\|^2$ and $\frac{\partial V_S}{\partial x} f(x, h(x)) \le -c_2 \|x\|^2$ on a compact set $\Omega_x \supset \{d_1\|x\|^2 \le D\}$.
3. **Stable boundary layer.** There is $V_B(x, y)$ with $d_3\|y\|^2 \le V_B \le d_4\|y\|^2$ and $\frac{\partial V_B}{\partial y} g(x, y + h(x), 0) \le -c_3\|y\|^2$.
4. **Interconnection bounds.** With $y = z - h(x)$, $\Delta_f(x,z)=f(x,z)-f(x,h(x))$ and $\Delta_g(x,z,\varepsilon)=g(x,z,\varepsilon)-g(x,z,0)$, there are constants $c_4,\dots,c_{12}\ge0$ such that, for all $x \in D_x$ and $y$ with $y + h(x) \in D_z$ (the source's (14)),

$$
\begin{aligned}
\frac{\partial V_S}{\partial x}\,\Delta_f(x, y+h(x)) &\le c_4\|x\|\|y\|,\\
\frac{\partial V_B}{\partial x}\,f(x, y+h(x)) &\le c_5\|y\|^2 + c_6\|x\|\|y\|,\\
\frac{\partial V_B}{\partial y}\,\Delta_g(x, y+h(x), \varepsilon) &\le \varepsilon\big(c_7\|y\|^2 + c_8\|x\|\|y\| + c_9\|y\|\big),\\
\Big|\frac{\partial V_B}{\partial y}\frac{\partial h}{\partial x}\,f(x, y+h(x))\Big| &\le c_{10}\|y\|^2 + c_{11}\|x\|\|y\| + c_{12}\|y\|.
\end{aligned}
$$

**Theorem.** Let $0 < \gamma, \delta < 1$ and start from $x_0 \in \{d_2\|x\|^2 \le \varrho D\}$ with $0 \le \varrho < 1$. Then there is $\varepsilon^*(\gamma, \delta) > 0$ such that for all $\varepsilon < \varepsilon^*$ the state $w(t) = (x(t), z(t) - h(0))$ satisfies

$$
\|w(t)\|^2 \le \beta(\|w(0)\|^2, t) + \mu(\varepsilon), \qquad t \ge 0,
$$

where $\beta$ is a class-$\mathcal{KL}$ function and $\mu(\varepsilon) \to 0$ as $\varepsilon \to 0$. Thus trajectories are ultimately bounded in a neighborhood of the equilibrium whose size vanishes with the time-scale separation, and $x(t)$ never leaves $\Omega_x$.

Unlike Tikhonov-type results this gives a bound on the infinite time interval without requiring an exact equilibrium of the perturbed system, which is the situation in models where $\varepsilon$ enters the fast dynamics through more than a time rescaling.

## Expansion

Use the composite Lyapunov function $\nu(x,y) = (1-\theta) V_S(x) + \theta V_B(x,y)$. Along trajectories, assumptions 2 and 3 give the negative terms $-c_2\|x\|^2$ and $-(c_3/\varepsilon)\|y\|^2$, while assumption 4 contributes cross terms of the form $k_1(\varepsilon)\|y\| + (\text{const})\|x\|\|y\|$, with $k_1$ built from $c_9$ and $c_{12}$. A quadratic-form argument shows that $\dot\nu \le 0$ outside a ball whose radius is of order $\varepsilon k_1(\varepsilon)$ plus $\sqrt{\varepsilon}\,k_1(\varepsilon)$, which shrinks as $\varepsilon \to 0$. A first step shows $x$ stays in $\Omega_x$ for small $\varepsilon$, so the local Lyapunov estimates apply globally in time; comparison then yields the $\mathcal{KL}$ bound for $(x, y)$, and $\|z - h(0)\| \le \|y\| + c_1\|x\|$ transfers it to $w$.

## Sources

- S. Waldherr and F. Allgöwer, *Network-level dynamics of diffusively coupled cells*, arXiv:1212.4270 (2012), Section 2.1, Assumptions 1–4, Lemma 1 and Theorem 1. <https://doi.org/10.48550/arXiv.1212.4270>
