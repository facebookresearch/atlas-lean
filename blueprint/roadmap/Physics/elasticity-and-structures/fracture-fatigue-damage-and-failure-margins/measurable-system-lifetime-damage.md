# System lifetime of measurable continuous monotone damage is measurable

Let $\Omega$ carry a σ-algebra and $E$ be a finite set of components. Suppose that for every
component $i$ and time $t \ge 0$ the damage $\omega \mapsto d_i(\omega, t)$ is measurable, every
threshold $\omega \mapsto D_i(\omega)$ is measurable, and every path $t \mapsto d_i(\omega, t)$ is
continuous and nondecreasing. Let $A$ be any event of
[configurations](../../../Probability/random-fields/spin-and-bond-configuration-spaces/config-space.md)
$x \in \{0, 1\}^E$, increasing or not. Then the system lifetime
$T(\omega) = \max_{x \in A} \min_{i : x_i = 1} \tau_i(\omega)$ (a maximum over no configuration is
$0$, a minimum over no component is $\infty$), with $\tau_i$ the
[damage lifetimes](damage-lifetime.md), is a measurable function of $\omega$ into $[0, \infty]$.
