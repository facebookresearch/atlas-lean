# Membership in the system failure event

Let $\Omega$ and $E$ be finite types, $S$ an increasing set of configurations $E \to \{\mathrm{false}, \mathrm{true}\}$ (an upper set for the order $\mathrm{false} < \mathrm{true}$), and $d_0, r, D : E \to \Omega \to \mathbb{R}$ with $r(i, \omega) \ge 0$ for all $i, \omega$. For every $t \in \mathbb{R}_{\ge 0}$ and every scenario $\omega$, $\omega$ lies in the system failure event $F_t$ of the linear damage paths exactly when the configuration

$$x_t(\omega) : i \mapsto \big[\, d_0(i, \omega) + r(i, \omega)\, t < D(i, \omega) \,\big]$$

of components still below their thresholds at time $t$ is not in $S$.
