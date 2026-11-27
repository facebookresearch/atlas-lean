# Hankel factorization of Markov parameters

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and $m, p \ge 1$. A **Markov sequence** is a sequence $\mathcal{A} = (\mathcal{A}_i)_{i \ge 1}$ of matrices in $\mathbb{K}^{p \times m}$; a triple $(A, B, C)$ with $A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$, $C \in \mathbb{K}^{p \times n}$ **realizes** it if $\mathcal{A}_i = C A^{i-1} B$ for all $i \ge 1$. For $s, t \ge 0$ the block Hankel matrix $H_{s,t}(\mathcal{A}) \in \mathbb{K}^{ps \times mt}$ has $(i, j)$ block $\mathcal{A}_{i+j-1}$; when $s = 0$ or $t = 0$ it is the empty matrix, of rank $0$. With the reachability and observability matrices $R_t(A, B)$ and $O_s(A, C)$, $s, t \ge 0$ (empty for $t = 0$, respectively $s = 0$):

1. $(A, B, C)$ realizes $\mathcal{A}$ if and only if $O_s(A, C)\, R_t(A, B) = H_{s,t}(\mathcal{A})$ for all $s, t \ge 0$ (the cases $s = 0$ or $t = 0$ are trivial identities between empty matrices); in that case also $O_s(A, C)\, A\, R_t(A, B)$ is the matrix $H_{s+1,t}(\mathcal{A})$ with its first block row removed.
2. If $(A_1, B_1, C_1)$ and $(A_2, B_2, C_2)$ have the same state dimension $n$ and the same Markov parameters, then, writing $R_i = R_n(A_i, B_i)$ and $O_i = O_n(A_i, C_i)$,

    $$O_1 R_1 = O_2 R_2, \qquad O_1 A_1 R_1 = O_2 A_2 R_2, \qquad O_1 B_1 = O_2 B_2, \qquad C_1 R_1 = C_2 R_2 .$$

3. If $(A, B, C)$ realizes $\mathcal{A}$ then $\operatorname{rank} H_{s,t}(\mathcal{A}) \le n$ for all $s, t \ge 0$, and if moreover $\operatorname{rank} R(A, B) = \operatorname{rank} O(A, C) = n$ then $\operatorname{rank} H_{s,t}(\mathcal{A}) = n$ whenever $s, t \ge n$ (for $n = 0$ the realized sequence is zero, so every $H_{s,t}(\mathcal{A})$ has rank $0$).

Part 2 is part 1 for $(s, t) = (n, n)$, the shifted identity with $(n, n)$, and part 1 with $(s, t) = (n, 1)$ and $(1, n)$, since $R_1 = B$ and $O_1 = C$; each identity compares blocks $C_1 A_1^{k} B_1 = C_2 A_2^{k} B_2$.

## Depends on

- [Reachability and null-controllability of discrete-time linear systems](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md): the matrices $R_t(A, B)$.
- [Observability of discrete-time linear systems over a finite horizon](../observability-of-linear-systems/observability-rank-condition-discrete-time.md): the matrices $O_s(A, C)$.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 6.5: the Hankel matrix (6.18), Lemma 6.5.5, Corollaries 6.5.6 and 6.5.7, identity (6.20) (p. 285), and their use with $(s, t) = (n, n), (n, 1), (1, n)$ in the proof of Theorem 27 (p. 287).
