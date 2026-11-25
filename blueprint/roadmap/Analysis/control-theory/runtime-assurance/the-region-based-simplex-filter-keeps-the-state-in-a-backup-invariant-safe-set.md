# The region-based simplex filter keeps the state in a backup-invariant safe set

Consider a discrete-time system $x(k+1) = F(x(k), u(k))$ with states $x \in X$ and inputs $u \in U$, a constraint set $C_A \subseteq X$, a backup control law $u_b : X \to U$, and a set $C_S \subseteq C_A$ that is **invariant under the backup law**: $F(x, u_b(x)) \in C_S$ for every $x \in C_S$. Given any sequence of desired inputs $u_{\mathrm{des}}(k) \in U$ (from an unverified primary controller), the **region-based simplex filter** applies

$$u(k) = \begin{cases} u_{\mathrm{des}}(k) & \text{if } F(x(k), u_{\mathrm{des}}(k)) \in C_S, \\ u_b(x(k)) & \text{otherwise.} \end{cases}$$

Then for every $x(0) \in C_S$ and every sequence of desired inputs, $x(k) \in C_S \subseteq C_A$ for all $k \ge 0$: the closed loop never violates the constraints, whatever the primary controller does.

**Proof.** By induction on $k$. If $x(k) \in C_S$, then either the desired input is applied, in which case $x(k+1) = F(x(k), u_{\mathrm{des}}(k)) \in C_S$ by the test, or the backup input is applied, in which case $x(k+1) = F(x(k), u_b(x(k))) \in C_S$ by invariance.

## Sources

- K. L. Hobbs, M. L. Mote, M. C. L. Abate, S. D. Coogan and E. M. Feron, "Runtime assurance for safety-critical systems: an introduction to safety filtering approaches for complex control systems", *IEEE Control Systems Magazine* 43(2), 2023, <https://arxiv.org/abs/2110.03506>, "The Simplex Architecture" (the monitor, backup controller and switching decision logic, pp. 27–28) and the explicit simplex filter, Algorithm 1 (region-based simplex filter, which accepts the desired input when the candidate next state lies in a set $C_S \subseteq C_A$ invariant under the backup law and otherwise applies the backup law, rendering the closed loop forward invariant in $C_S$, pp. 32–33).
