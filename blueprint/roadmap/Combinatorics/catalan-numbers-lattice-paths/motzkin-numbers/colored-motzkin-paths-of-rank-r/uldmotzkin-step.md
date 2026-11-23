# Colored Motzkin steps of a given rank

Let $r$ and $l$ be natural numbers and let
$u, d \colon \{0, \dots, r - 1\} \to \mathbb{N}$. The admissible steps of rank $r$ are the
up-steps $U_j$ with $0 \le j < r$ in one of $u(j)$ colors, the level steps in one of $l$ colors,
and the down-steps $D_j$ with $0 \le j < r$ in one of $d(j)$ colors: the disjoint union of the
sets $\{j\} \times \{0, \dots, u(j) - 1\}$ for $j < r$, the set $\{0, \dots, l - 1\}$, and the
sets $\{j\} \times \{0, \dots, d(j) - 1\}$ for $j < r$.

A step kind with zero colors contributes no steps. The steps $U_j$ and $D_j$ have jump size
$j + 1$, so no up- or down-step has jump size zero.
