# Controller-form realization of a proper rational transfer matrix

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. Let $G(s) = D + N(s)/d(s)$ be a proper rational $p \times m$ matrix in common-denominator form. Here $D \in \mathbb{K}^{p \times m}$, $d(s) = s^r + d_{r-1} s^{r-1} + \dots + d_1 s + d_0$ is monic of degree $r \ge 1$, and $N(s) = N_0 + N_1 s + \dots + N_{r-1} s^{r-1}$ with $N_i \in \mathbb{K}^{p \times m}$, so $\deg N < r$. Define the block controller form, with $I = I_m$:

$$A = \begin{bmatrix} 0 & I & 0 & \cdots & 0 \\ 0 & 0 & I & \cdots & 0 \\ \vdots & & & \ddots & \vdots \\ 0 & 0 & 0 & \cdots & I \\ -d_0 I & -d_1 I & -d_2 I & \cdots & -d_{r-1} I \end{bmatrix} \in \mathbb{K}^{rm \times rm}, \quad B = \begin{bmatrix} 0 \\ \vdots \\ 0 \\ I \end{bmatrix}, \quad C = \begin{bmatrix} N_0 & N_1 & \cdots & N_{r-1} \end{bmatrix}.$$

1. $\det(sI - A) = d(s)^m$, For $m\ge1$, $sI - A$ is invertible exactly when $d(s) \ne 0$. For $m=0$ the state space is zero dimensional and $sI-A$ is always invertible; the determinant and $d(s)^0$ are both $1$.
2. **As rational matrices,** $C (sI - A)^{-1} B + D = G(s)$, and the identity holds at every $s \in \mathbb{C}$ with $d(s) \ne 0$. For real coefficients, evaluation at a complex $s$ uses complexification. If $m\ge1$, at a root of $d$ the resolvent is not defined, even when the transfer matrix has a removable singularity there. The displayed evaluated identity is asserted only off those roots.
3. The pair $(A, B)$ is controllable. The construction does not cancel common factors and need not be observable or minimal. For example, $N=0$, $r=m=1$ gives $C=0$ and a one-state realization of the constant matrix $D$, which also has a zero-state realization.
4. Separately, in the degree-zero denominator case $r=0$, $d=1$ and $N=0$, so $G=D$ is constant; the realization has state dimension $0$ and output $y = Du$.

**Single-input single-output case** ($m = p = 1$). For $n\ge1$, let $q(s) = s^n + q_{n-1} s^{n-1} + \dots + q_0$ be monic and let $\deg \pi \le n$. Let $\delta$ be the coefficient of $s^n$ in $\pi$; then $\rho = \pi - \delta q$ has $\deg \rho < n$, $\rho(s) = \rho_0 + \dots + \rho_{n-1} s^{n-1}$. With $A$ the companion matrix of $q$ (last row $-q_0, \dots, -q_{n-1}$), $b = e_n$ and $c = (\rho_0, \dots, \rho_{n-1})$, we get $c (sI - A)^{-1} b + \delta = \pi(s)/q(s)$ as rational functions and at every $s$ with $q(s) \ne 0$. This $(A, b)$ is the controller form of Sontag's Definition 5.1.5. For $n=0$, $q=1$ and $\pi$ is constant, so use the zero-state realization above.

The following block calculation proves the transfer identity; it is a direct derivation, not a claim that the source displays this particular MIMO realization. The block column $X(s) = d(s)^{-1} \begin{bmatrix} I & sI & \cdots & s^{r-1} I \end{bmatrix}^\top$ satisfies $(sI - A) X(s) = B$. Rows $1, \dots, r-1$ give $s \cdot s^{i-1} - s^i = 0$, and the last row gives $(s^r + d_{r-1} s^{r-1} + \dots + d_0)/d(s) = 1$. Therefore $(sI - A)^{-1} B = X(s)$ and $C X(s) = N(s)/d(s)$. Up to a permutation of coordinates, $A$ is $m$ copies of the companion matrix of $d$, which gives part 1. The block reachability matrix $[B,AB,\dots,A^{r-1}B]$ has identity blocks on its reversed block diagonal and zeros above that diagonal before reversal, so reversing its block rows makes it block triangular with identity diagonal. It has rank $rm$, proving controllability (also vacuously for $m=0$).

## Depends on

- [Reachability and null-controllability of discrete-time linear systems](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md): the reachability matrix and the meaning of a controllable pair.

## Proof depends on

- [Reachability and null-controllability of discrete-time linear systems](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md): the full-rank criterion used when $m\ge1$; for $m=0$ the state space is zero and controllability is immediate.

## Background

- [Hankel factorization of Markov parameters](hankel-factorization-of-markov-parameters.md): the Markov-sequence viewpoint on realization; its factorization theorem is not used in the block resolvent calculation.

- [Minimal realizations are exactly the canonical ones](minimal-realizations-are-canonical.md): a minimal realization is controllable and observable; this one is controllable

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Definition 5.1.5 (controller form, p. 184) and Lemma/Exercise 5.1.6 (its pair is controllable with characteristic polynomial the given one, p. 185); Section 6.7: Proposition 6.7.1 (a Markov sequence is realizable if and only if its generating series is rational, p. 298) and Remark 6.7.4 ($(sI - A)^{-1} = \sum_{i \ge 1} A^{i-1} s^{-i}$, so $C(sI - A)^{-1}B$ is the generating series, p. 299).
