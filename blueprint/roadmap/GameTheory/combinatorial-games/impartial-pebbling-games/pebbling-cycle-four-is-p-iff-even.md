# Parity decides $(2:1)$-pebbling on $C_4$ in $\hat X_{aabb} \cup X_{abac}$

Consider the
$(2:1)$-pebbling game on the cycle $C_4$ with vertices $v_0, v_1, v_2, v_3$, where $v_i$ is
adjacent to $v_{i \pm 1}$ (indices mod $4$), and let $a = (a_0, a_1, a_2, a_3)$ be a position
with $a_i$ pebbles on $v_i$. Suppose that $a$ lies in $\hat X_{aabb} \cup X_{abac}$, where
$\hat X_{aabb}$ means that for some $i \in \{0, 1\}$, $a_i \equiv a_{i+1}$ and
$a_{i+2} \equiv a_{i-1} \pmod 3$, and $X_{abac}$ means that for some $i \in \{0, 1\}$,
$a_i \equiv a_{i+2} \pmod 3$ and $a_i$, $a_{i+1}$, $a_{i-1}$ are pairwise incongruent mod $3$.
Then $a$ is a P-position if and only if $a_0 + a_1 + a_2 + a_3$ is even.

## Sources

- Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024), Article 24.5.8, Theorem 16.
