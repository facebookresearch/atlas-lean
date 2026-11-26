# The safe backward image of a backup-invariant set is invariant under the backup law

Consider $x(k+1) = F(x(k), u(k))$ with a backup control law $u_b$, let $\phi(i; x)$ be the state reached after $i$ steps under $u_b$ from $x$, let $C_A$ be a constraint set, and let $C_b \subseteq C_A$ be invariant under the backup law: $\phi(1; x) \in C_b$ for every $x \in C_b$. For a horizon $N \ge 1$ let

$$C_S = \{x \in X : \phi(i; x) \in C_A \text{ for } i = 0, \dots, N - 1, \text{ and } \phi(N; x) \in C_b\}.$$

Then:

1. $C_b \subseteq C_S \subseteq C_A$;
2. $C_S$ is invariant under the backup law: $\phi(1; x) \in C_S$ for every $x \in C_S$;
3. consequently, the simulation-based simplex filter, which applies a desired input $u_{\mathrm{des}}$ when $F(x, u_{\mathrm{des}}) \in C_S$ and $u_b(x)$ otherwise, keeps every trajectory starting in $C_S$ inside $C_S$, and so inside $C_A$.

Membership in $C_S$ is checked by simulating $N$ steps of the backup law, so the backup set $C_b$ can be much smaller than the region $C_S$ the filter allows.

**Proof.** For part 1, a point of $C_b$ stays in $C_b \subseteq C_A$ under the backup law, and $i = 0$ gives $C_S \subseteq C_A$. For part 2, let $x \in C_S$ and $y = \phi(1; x)$, so that $\phi(i; y) = \phi(i + 1; x)$. For $i \le N - 2$ this lies in $C_A$; for $i = N - 1$ it equals $\phi(N; x) \in C_b \subseteq C_A$; and $\phi(N; y) = \phi(1; \phi(N; x)) \in C_b$ by the invariance of $C_b$. Part 3 is the induction of the runtime safety shield with $C_S$ as the recoverable set and no disturbance.

## Proof depends on

- [Runtime safety shield (simplex) over discrete dynamics](../runtime-safety-shield-over-discrete-dynamics.md): the shield keeps the state in any set invariant under the fallback law

## Sources

- K. L. Hobbs, M. L. Mote, M. C. L. Abate, S. D. Coogan and E. M. Feron, "Runtime assurance for safety-critical systems: an introduction to safety filtering approaches for complex control systems", *IEEE Control Systems Magazine* 43(2), 2023, <https://arxiv.org/abs/2110.03506>, the implicit simplex filter: Algorithm 2 (simulation-based simplex filter) and the safe backward image (26) of a backup set $C_b \subseteq C_A$ invariant under the backup law, stated to be forward invariant under the backup law so that the filter renders the closed loop forward invariant in it (pp. 34–35). The invariance proof is written out on the page.
