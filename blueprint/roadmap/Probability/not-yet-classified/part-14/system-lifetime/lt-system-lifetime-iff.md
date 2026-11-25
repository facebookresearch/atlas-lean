# System survives past t iff the up configuration lies in the event

Let $E$ be a finite set of components with lifetimes $T_e \in [0, \infty]$, and let $A$ be an increasing set of up/down configurations (if $x \in A$ and $x \le x'$ coordinatewise then $x' \in A$). Define the system lifetime $\tau_A = \max_{x \in A} \min_{e : x_e = \mathrm{up}} T_e$. For every finite time $t \ge 0$, $t < \tau_A$ if and only if the configuration with component $e$ up exactly when $t < T_e$ lies in $A$.
