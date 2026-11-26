# Diffusion limit of kinetic chemotaxis in slab geometry with an O(ε) rate

**Kinetic model.** Let $X = (0, \ell)$ be the gap between two parallel membranes, $V = (-1, 1)$ the set of velocities and $Q = X \times V$ the phase space, with inflow boundary $\Gamma^{in} = \{0\} \times (0,1) \cup \{\ell\} \times (-1, 0)$. For a parameter $\varepsilon > 0$ (inverse tumbling rate), a cell density $u^\varepsilon(x, v, t)$ and a chemoattractant $c^\varepsilon(x, t)$ solve

$$
\begin{aligned}
\varepsilon^2 \partial_t u^\varepsilon + \varepsilon v\, \partial_x u^\varepsilon + \sigma(x)\,(u^\varepsilon - \bar u^\varepsilon) &= \varepsilon \alpha\, v\, \partial_x c^\varepsilon\, \bar u^\varepsilon && \text{in } Q \times (0, T),\\
\partial_t c^\varepsilon - D\,\partial_{xx} c^\varepsilon + \beta c^\varepsilon &= \gamma \bar u^\varepsilon && \text{in } X \times (0, T),
\end{aligned}
$$

where $\bar u^\varepsilon = \tfrac12 \int_V u^\varepsilon\,\mathrm{d}v$ is the velocity average, with velocity-independent data $u^\varepsilon = \bar g_u$ on $\Gamma^{in}$, $c^\varepsilon = \bar g_c$ on $\partial X$, $u^\varepsilon(0) = \bar u_0$, $c^\varepsilon(0) = \bar c_0$.

**Hypotheses.** $\alpha, \beta, \gamma \ge 0$, $D > 0$; the tumbling rate satisfies $0 < \sigma_{\min} \le \sigma(x) \le \sigma_{\max}$; $\bar u_0 \in H^2(X)$, $\bar c_0 \in H^4(X)$; $\bar g_u, \bar g_c \in W^{2,\infty}(0, T^*; \mathbb{R}^2)$ and the data are compatible.

**Theorem (uniform local well-posedness).** There is $T > 0$ such that for all $0 < \varepsilon \le \varepsilon^*$ the kinetic system has a unique solution $u^\varepsilon \in C^1([0,T]; L^2(Q))$ with $v\,\partial_x u^\varepsilon \in C^0([0,T]; L^2(Q))$ and $c^\varepsilon \in H^2(0,T; L^2(X)) \cap H^1(0,T; H^2(X))$, and, uniformly in $\varepsilon$, $\|u^\varepsilon\|_{C^0(L^2(Q))} \le C$, $\|u^\varepsilon - \bar u^\varepsilon\|_{L^2(L^2(Q))} \le C\varepsilon$ and the outflow trace satisfies $\|u^\varepsilon - \bar g_u\|_{L^2(L^2(\Gamma^{out}; |v|\,\mathrm{d}\Gamma))} \le C\sqrt{\varepsilon}$.

**Theorem (Keller-Segel limit and rate).** As $\varepsilon \to 0$, $u^\varepsilon \rightharpoonup \bar u^0$ weakly in $L^2(0,T; L^2(Q))$ and $c^\varepsilon \to c^0$ in $L^2(0,T; H^1(X))$, where $(\bar u^0, c^0)$ is the unique weak solution of

$$
\partial_t \bar u^0 - \partial_x\big(\bar\mu\, \partial_x \bar u^0 - \bar\chi\, \partial_x c^0\, \bar u^0\big) = 0, \qquad \partial_t c^0 - D\,\partial_{xx} c^0 + \beta c^0 = \gamma \bar u^0,
$$

with Dirichlet data $\bar g_u, \bar g_c$ and coefficients

$$
\bar\mu(x) = \frac{1}{\sigma(x)} \cdot \frac12 \int_{-1}^{1} v^2\,\mathrm{d}v = \frac{1}{3\sigma(x)}, \qquad \bar\chi(x) = \alpha\, \bar\mu(x).
$$

If moreover $\sigma \in W^{1,\infty}(X)$, then (with the data-lifted variables) $\|u^\varepsilon - \bar u^0\|_{L^\infty(L^2(Q))} + \|c^\varepsilon - c^0\|_{L^\infty(H^1(X))} \le C\varepsilon$ with $C$ independent of $\varepsilon$.

## Expansion

The kinetic operator $\mathcal{A}^\varepsilon w = \varepsilon^{-1} v\,\partial_x w + \varepsilon^{-2} \sigma (w - \bar w)$ with homogeneous inflow data is maximal monotone on $L^2(Q)$, so the linearized problem is solved by a contraction semigroup; a fixed-point map $z \mapsto (\bar c, u)$, where $\bar c$ solves the parabolic equation with source $\gamma \bar z$ and $u$ solves the kinetic equation with drift $\partial_x \bar c$, is a contraction on a short time interval chosen independently of $\varepsilon$. The energy identity, with the boundary term $\int_{\Gamma^{out}} - \int_{\Gamma^{in}}$ weighted by $|v|$, gives the $\varepsilon$-uniform bounds; the relaxation term controls $u^\varepsilon - \bar u^\varepsilon$ at order $\varepsilon$. Integrating the kinetic equation against $1$ and $v$ gives the moment system: the flux $j^\varepsilon = \tfrac{1}{2\varepsilon}\int_V v u^\varepsilon\,\mathrm{d}v$ satisfies $j^\varepsilon = -\bar\mu\, \partial_x \bar u^\varepsilon + \bar\chi\, \partial_x c^\varepsilon \bar u^\varepsilon + O(\varepsilon)$, which produces the Keller-Segel limit. The rate follows by comparing $u^\varepsilon$ with the Chapman-Enskog ansatz $\bar u^0 - \varepsilon \sigma^{-1} v(\partial_x \bar u^0 - \alpha \partial_x c^0 \bar u^0)$ and absorbing the boundary-layer terms. A difficulty specific to the slab is that velocities near $0$ are tangent to the membranes, so outflow traces are controlled only in the weighted measure $|v|\,\mathrm{d}\Gamma$.

## Sources

- Herbert Egger, Kathrin Hellmuth, Nora Philippi and Matthias Schlottbom, "A kinetic chemotaxis model and its diffusion limit in slab geometry", arXiv (2024), Section 2 (model and Assumption 1), Theorem 2 (well-posedness and uniform bounds), Theorem 3 (Keller-Segel limit and convergence rate), Propositions 4, 5, 8 and 10, <https://doi.org/10.48550/arXiv.2408.17243>.
