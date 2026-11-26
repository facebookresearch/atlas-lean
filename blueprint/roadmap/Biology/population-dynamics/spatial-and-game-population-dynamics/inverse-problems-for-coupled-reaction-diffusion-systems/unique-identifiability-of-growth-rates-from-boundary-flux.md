# Unique identification of growth-rate coefficients in a coupled population system from average boundary flux

Let $\Omega \subset \mathbb{R}^N$ be a bounded domain with smooth boundary, $T > 0$, $D_T = \Omega \times (0, T]$, $S_T = \partial\Omega \times (0, T]$, and $\Gamma_T = \Lambda \times (0, T]$ for a nonempty open $\Lambda \subset \partial\Omega$ with outward unit normal $\nu$. Fix $\gamma \in (0, 1)$, diffusivities $d_1, d_2 > 0$, constant drift vectors $\alpha, \beta \in \mathbb{R}^N$ and an integer $M \ge 1$. For coefficients $l, v \in C^{\gamma, \gamma/2}(D_T)$ and inputs $a_1, a_2, q_1, q_2 \in C^{\gamma,\gamma/2}(D_T)$ consider the coupled system for two population densities $u, m \ge 0$:

$$\begin{aligned}
\partial_t u - d_1 \Delta u + \alpha \cdot \nabla u &= l(x,t)\, u + a_1\Big(-u^2 - \sum_{k=1}^{M} u^k m^{M-k+1}\Big) + q_1 && \text{in } D_T,\\
\partial_t m - d_2 \Delta m + \beta \cdot \nabla m &= v(x,t)\, m + a_2\Big(-m^2 - \sum_{k=1}^{M} u^k m^{M-k+1}\Big) + q_2 && \text{in } D_T,
\end{aligned}$$

with $u = m = 0$ on $S_T$ and $u(\cdot, 0) = m(\cdot, 0) = 0$ in $\Omega$. For positive $a_i, q_i$ this system has a unique positive solution (Ding, Liu and Zheng 2023, Theorem 3.2). Given nonnegative, nonzero weights $h, g \in C_0^{\gamma,\gamma/2}(\Gamma_T)$, the **average flux measurements** are

$$F^{+}_{l,v}(a_1, a_2, q_1, q_2) = \int_{\Gamma_T} \frac{\partial u}{\partial \nu}\, h \, dx\, dt, \qquad G^{+}_{l,v}(a_1, a_2, q_1, q_2) = \int_{\Gamma_T} \frac{\partial m}{\partial \nu}\, g \, dx\, dt.$$

A sequence $(a^s)_{s \ge 1}$ is **admissible**, $(a^s) \in \mathcal{A}$, if each $a^s \in C^{\gamma,\gamma/2}(D_T)$ is positive and $a^s \to 0$; a sequence $(q^n)_{n \ge 1}$ is admissible, $(q^n) \in \mathcal{B}$, if each $q^n \in C^{\gamma,\gamma/2}(D_T)$ is positive and $\{q^n\}$ is complete in $L^2(D_T)$.

Measurements with weight $h$ carry no information about times after the support of $h$ ends. Let

$$\tau_h = \sup\{t \in (0, T] : h(\cdot, t) \not\equiv 0 \text{ on } \Lambda\}, \qquad \tau_g = \sup\{t \in (0, T] : g(\cdot, t) \not\equiv 0 \text{ on } \Lambda\}.$$

**Theorem (after Ding, Liu and Zheng 2023, Theorem 4.1).** Let $l_1, v_1, l_2, v_2 \in C^{\gamma,\gamma/2}(D_T)$ be negative functions. If

$$F^{+}_{l_1,v_1}(a_1^s, a_2^s, q_1^n, q_2^n) = F^{+}_{l_2,v_2}(a_1^s, a_2^s, q_1^n, q_2^n), \qquad G^{+}_{l_1,v_1}(a_1^s, a_2^s, q_1^n, q_2^n) = G^{+}_{l_2,v_2}(a_1^s, a_2^s, q_1^n, q_2^n)$$

for all $s, n \in \mathbb{N}$, with $(a_i^s) \in \mathcal{A}$ and $(q_i^n) \in \mathcal{B}$, then $l_1 = l_2$ in $\Omega \times (0, \tau_h)$ and $v_1 = v_2$ in $\Omega \times (0, \tau_g)$. In particular both pairs agree on all of $D_T$ when $\tau_h = \tau_g = T$.

Nothing can be recovered after $\tau_h$ or $\tau_g$, whatever the inputs. If both weights are supported in $t \le T/2$, take two smooth coefficient pairs that agree on $\Omega \times (0, T/2]$ and differ afterwards: by forward uniqueness the solutions agree up to $T/2$ for every input, so every listed flux measurement agrees, although the coefficients differ. Completeness of the inputs does not compensate for unobserved times. The source states the conclusion on all of $D_T$ without this restriction.

## Expansion

Letting $s \to \infty$ switches off the competition terms, so the measurements of the linearized system, driven by the sources $q_i^n$, coincide for the two coefficient pairs. For the linear problem, multiply the difference of the two solutions by the solution $w$ of the adjoint problem $-\partial_t w - d_1\Delta w - \alpha\cdot\nabla w - l_1 w = 0$ with $w = h_0$ on $S_T$ ($h_0 = h$ on $\Gamma_T$, $0$ elsewhere) and $w(\cdot, T) = 0$, and integrate by parts: equal fluxes give $\int_{D_T} (l_1 - l_2)\, u_2\, w \, dx\, dt = 0$ type identities for every source $q^n$. Completeness of $\{q^n\}$ in $L^2(D_T)$ and positivity of $u_2$ (from the positive inputs and the maximum principle) then give $(l_1 - l_2)\,w = 0$. The backward problem for $w$ has zero data on $(\tau_h, T]$, so $w \equiv 0$ there, while the strong maximum principle makes $w > 0$ in $\Omega \times (0, \tau_h)$ because $h_0 \ge 0$ is nonzero on $(t, \tau_h)$ for every $t < \tau_h$. This is exactly where $l_1 = l_2$ follows; the argument for $v$ is symmetric. Positivity of the inputs is what guarantees the solutions stay in the biologically meaningful nonnegative cone throughout.

## Sources

- M.-H. Ding, H. Liu and G.-H. Zheng, "On inverse problems for several coupled PDE systems arising in mathematical biology", Journal of Mathematical Biology 87 (2023), 86, system (1.1), measurements (1.2)–(1.3), Definitions 4.1–4.2 and Theorem 4.1 (stated there on all of $D_T$), <https://doi.org/10.1007/s00285-023-02021-4>.
