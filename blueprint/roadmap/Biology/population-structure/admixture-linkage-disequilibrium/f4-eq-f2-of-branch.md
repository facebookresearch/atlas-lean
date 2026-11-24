# f4 equals f2 for references branching off the path

Let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights $w$, and let $A, B, A', B', A'', B''$ be populations and $u_A, u_B, u_{A'}, u_{B'} \in \mathbb{R}^E$ with

$$w(A, \cdot) = w(A'', \cdot) + u_A,\quad w(B, \cdot) = w(B'', \cdot) + u_B,\quad w(A', \cdot) = w(A'', \cdot) + u_{A'},\quad w(B', \cdot) = w(B'', \cdot) + u_{B'},$$

such that for every edge $e$: $u(e)\, v(e) = 0$ for $u \in \{u_A, u_B\}$ and $v \in \{u_{A'}, u_{B'}\}$, and $\bigl(w(A'', e) - w(B'', e)\bigr) u(e) = 0$ for each $u \in \{u_A, u_B, u_{A'}, u_{B'}\}$. Then

$$f_4(A, B; A', B') = f_2(A'', B''),$$

for the [f2](../patterson-s-f-statistics/f2.md) and [f4](../patterson-s-f-statistics/f4.md) statistics of the population frequencies. On a tree the hypotheses say that the paths $A''$–$B''$, $A''$–$A$, $B''$–$B$, $A''$–$A'$ and $B''$–$B'$ share no edge in the stated pairs.
