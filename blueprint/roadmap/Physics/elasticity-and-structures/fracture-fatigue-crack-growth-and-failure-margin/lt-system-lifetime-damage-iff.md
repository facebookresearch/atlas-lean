# A monotone system is up at $t$ iff its below-threshold set is in $A$

Let $E$ be a finite set of components, each $i \in E$ with damage paths $d_i(\omega, \cdot)$ that
are continuous and nondecreasing on $[0, \infty)$ for every $\omega$, thresholds $D_i(\omega)$ and
[lifetimes](damage-lifetime.md) $\tau_i(\omega)$. Let $A$ be an
[increasing event](../../../Probability/correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md) of
[configurations](../../../Probability/random-fields/spin-and-bond-configuration-spaces/config-space.md)
$x \in \{0, 1\}^E$ (a monotone system, not necessarily coherent: $\emptyset$, all configurations
and systems with irrelevant components are allowed). For every outcome $\omega$ and finite time
$t \ge 0$, the system lifetime $T(\omega) = \max_{x \in A} \min_{i : x_i = 1} \tau_i(\omega)$ (a
maximum over no configuration is $0$, a minimum over no component is $\infty$) satisfies

$$t < T(\omega) \iff x(t) \in A,$$

where $x(t)_i = 1$ exactly when $d_i(\omega, t) < D_i(\omega)$: the system is up at $t$ exactly
when the configuration of the components whose damage is still below threshold lies in $A$.
