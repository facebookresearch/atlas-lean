# System failure event under linear damage

Let $\Omega$ be a finite type of scenarios and $E$ a finite type of components. A configuration is a map $x : E \to \{\mathrm{false}, \mathrm{true}\}$ ($\mathrm{true}$ meaning the component is up). Given a set $S$ of configurations, real data $d_0, r, D : E \to \Omega \to \mathbb{R}$ and a time $t \in \mathbb{R}_{\ge 0}$, let $\tau_i(\omega) \in [0, \infty]$ be the damage lifetime of component $i$ with linear damage path $s \mapsto d_0(i, \omega) + r(i, \omega)\, s$ against the threshold $D(i, \omega)$. The system failure event is the finite set

$$F_t = \{\omega \in \Omega : T_S(\tau(\omega)) \le t\},$$

where the system lifetime is $T_S(\tau) = \max_{x \in S} \min_{i : x(i) = \mathrm{true}} \tau_i$, with the minimum over no components equal to $\infty$ and the maximum over an empty $S$ equal to $0$.
