# Open Michaelis–Menten mechanism with substrate inflow

**Model.** Substrate $S$ flows in at constant rate $k_0 \ge 0$ and is converted by enzyme $E$ through a complex $C$: $\varnothing \xrightarrow{k_0} S$, $S + E \underset{k_{-1}}{\overset{k_1}{\rightleftharpoons}} C \xrightarrow{k_2} E + P$. With total enzyme $e_T = e + c$ conserved, mass action gives on the first quadrant

$$\dot s = k_0 - k_1(e_T - c)s + k_{-1}c, \qquad \dot c = k_1(e_T - c)s - (k_{-1} + k_2)c. \tag{2.4}$$

The open standard quasi-steady-state approximation (sQSSA) replaces $c$ by $w(s) = k_1 e_T s/(k_1 s + k_{-1} + k_2)$, giving $\dot s = k_0 - k_2 e_T s/(K_M + s)$ with $K_M = (k_{-1} + k_2)/k_1$.

1. **Equilibria and invariance.** The first quadrant is positively invariant and solutions exist for all $t \ge 0$; if $k_{-1} + k_2 > 0$ they enter the invariant strip $c \le e_T$. Under the genericity conditions $k_1 \ne 0$, $k_2 \ne 0$, $k_2 e_T \ne k_0$ there is exactly one stationary point

$$P_0 = \Bigl(\frac{(k_{-1} + k_2)k_0}{k_1(k_2 e_T - k_0)},\ \frac{k_0}{k_2}\Bigr),$$

lying in the first quadrant (an attracting node) iff $k_2 e_T > k_0$ and in the second quadrant (a saddle) iff $k_2 e_T < k_0$. There are no non-constant periodic orbits.
2. **Global dynamics.** If $k_2 e_T > k_0$, every solution in the first quadrant converges to $P_0$. If $k_2 e_T < k_0$ (inflow exceeds the maximal clearance rate), every solution in the first quadrant has $s(t) \to \infty$ with $c(t) \to e_T$: substrate accumulates without bound while the enzyme saturates. In each case a unique distinguished trajectory (through a saddle at infinity, or from $P_0$ to infinity) is a natural candidate for a global slow manifold.
3. **QSS parameter values.** Let $\psi(s,c) = k_1(e_T - c)s - (k_{-1} + k_2)c$. The QSS curve, the graph $c = w(s)$ of the source's Eq. (4.1), is the relevant component of the zero set $\psi = 0$ of Eq. (4.2); it is invariant for (2.4) exactly when $e_T = 0$, or $k_1 = 0$, or $k_0 = k_2 = 0$, or $k_{-1} = k_2 = 0$. In the last case $\psi = k_1(e_T - c)s$ is reducible: the component $\{c = e_T\}$, which is the graph $c = w(s) = e_T$ for $s > 0$, is invariant, but the component $\{s = 0\}$ is not when $k_0 k_1 e_T \ne 0$ (there $\dot s = k_0$), so the full zero set is not; for instance with $k_0 = k_1 = e_T = 1$ the solution through $(0,0)$ leaves $\{s(1-c) = 0\}$. The singular-perturbation (Tikhonov–Fenichel) parameter values relevant to the sQSSA are $k_0 = e_T = 0$ with the other rates positive, so in contrast to the closed mechanism QSS reduction is justified on a wider parameter set ($e_T$ small, $k_0$ not small) than singular perturbation reduction.
4. **Approach to the QSS curve.** On a suitable invariant wedge around $\psi = 0$, the squared distance to the QSS curve relaxes with fast time constant $(k_{-1} + k_2)^{-1}$ to a level of order $\varepsilon_*^2$, where

$$\varepsilon_* = \frac{k_0\, k_1 e_T}{(k_{-1} + k_2)^2}.$$

## Expansion

Adding the two equations gives $\dot s + \dot c \le k_0$, so solutions stay bounded on finite intervals, and $\dot c \le -(k_{-1} + k_2)e_T$ whenever $c \ge e_T$, giving the strip. In the strip the divergence $-(k_1(e_T - c) + k_1 s + k_{-1} + k_2)$ is negative, so Bendixson's criterion excludes periodic orbits; together with the unique node this gives convergence to $P_0$ when $k_2 e_T > k_0$. When $k_2 e_T < k_0$ the only finite equilibrium leaves the quadrant, and compactifying on the Poincaré sphere shows the point at infinity in the direction $c = e_T$ attracts the quadrant. For item 3, the Lie derivative of $\psi$ along (2.4) restricted to $\psi = 0$, where $\dot c = \psi = 0$ and $\dot s = k_0 - k_2 c$, equals $\partial_s\psi\,\dot s = k_1(e_T - c)(k_0 - k_2 c)$, and invariance requires this to vanish on the whole curve, which yields the listed cases. For $k_{-1} = k_2 = 0$ it equals $k_0 k_1 (e_T - c)$, which vanishes on the component $c = e_T$ but equals $k_0 k_1 e_T$ on the component $s = 0$ (the value $1$ at the origin in the example above), so only the first component is invariant. Taking $\varepsilon_*$ small (for instance small total enzyme relative to $K_M$ with moderate inflow) justifies replacing $c$ by $w(s)$ after a fast transient of duration about $(k_{-1} + k_2)^{-1}$, and higher-order slow-manifold expansions show the singular-perturbation regime gives the more accurate reduction.

## Sources

- J. Eilertsen, M. R. Roussel, S. Schnell, S. Walcher, "On the quasi-steady-state approximation in an open Michaelis–Menten reaction mechanism", *AIMS Mathematics* (2021), Sections 2–6 (Eqs. (2.4), (2.8), (3.1)–(3.3), (4.1)–(4.4), (4.16), Lemmas 1–2, Propositions 1–3, Remarks 1–2 and 4), <https://doi.org/10.3934/math.2021398> (PMC8208640).
