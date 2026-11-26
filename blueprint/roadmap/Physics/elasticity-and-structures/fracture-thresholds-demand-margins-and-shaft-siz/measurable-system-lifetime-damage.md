# Measurability of the system lifetime under damage

Let $\Omega$ carry a σ-algebra, $E$ be a finite type of components and $A$ any set of configurations $E \to \{\mathrm{false}, \mathrm{true}\}$. Let $d : E \to \Omega \to \mathbb{R}_{\ge 0} \to \mathbb{R}$ with $\omega \mapsto d(i, \omega, t)$ measurable for all $i, t$, let each $D(i, \cdot)$ be measurable, and let every path $t \mapsto d(i, \omega, t)$ be continuous and nondecreasing. Then $\omega \mapsto T_A(\tau(\omega))$ is measurable, where $\tau_i$ is the damage lifetime of component $i$ and $T_A(\tau) = \max_{x \in A} \min_{i : x(i) = \mathrm{true}} \tau_i$.

The [damage lifetime](damage-lifetime.md) of a path against a threshold is the first time $t \ge 0$ at which the damage is at least the threshold, and $\infty$ if there is none. The maximum over an empty set of configurations is $0$, and the minimum over a configuration with no working components is $\infty$.
