# Observability of discrete-time linear systems over a finite horizon

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $n \ge 0$ and $m, p \ge 1$, and let $A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$ and $C \in \mathbb{K}^{p \times n}$. Consider

$$x(t+1) = A\,x(t) + B\,u(t), \qquad y(t) = C\,x(t), \qquad t = 0, 1, 2, \dots .$$

For a known input sequence, $y(k) = C A^k x(0) + \sum_{j=0}^{k-1} C A^{k-1-j} B\, u(j)$, so after subtracting the known input term the outputs $y(0), \dots, y(N-1)$ determine $O_N(A, C)\, x(0)$, where for $N \ge 0$

$$O_N(A, C) = \begin{bmatrix} C \\ C A \\ \vdots \\ C A^{N-1} \end{bmatrix} \in \mathbb{K}^{pN \times n}, \qquad O(A, C) = O_n(A, C);$$

for $N = 0$ this is the empty $0 \times n$ matrix, whose kernel is $\mathbb{K}^n$ and whose rank is $0$.

Write $M^*$ for the conjugate transpose (the transpose when $\mathbb{K} = \mathbb{R}$). Then:

1. **Finite horizon.** For every $N \ge 1$ and every known input sequence, the map from the initial state $x(0)$ to the outputs $y(0), \dots, y(N-1)$ is injective if and only if $O_N(A, C)$ has rank $n$ (full column rank); the initial states that produce the same outputs as $x(0) = 0$ under zero input form the kernel of $O_N(A, C)$.
2. **Duality.** $O_N(A, C)^* = R_N(A^*, C^*)$, so $O_N(A, C)$ has rank $n$ if and only if every state can be steered to every state in exactly $N$ steps by the system $x^+ = A^* x + C^* v$ (the reachability criterion of [discrete-time reachability](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md)).
3. **Saturation and the rank condition.** For $N \ge n$ the kernel of $O_N(A, C)$ equals that of $O_n(A, C)$. Hence the system is observable (two initial states giving the same outputs under the same input are equal) if and only if $\operatorname{rank} O(A, C) = n$, and then the outputs $y(0), \dots, y(n-1)$ already determine the initial state.

Since the rank of a matrix equals that of its conjugate transpose, and also that of its transpose, the condition in part 3 is also equivalent to $\operatorname{rank} R(A^\top, C^\top) = n$, the form in which Sontag states the duality.

## Depends on

- [Reachability and null-controllability of discrete-time linear systems](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md): the matrices $R_N$ and the reachability criterion used in part 2.

## Proof depends on

- [Reachability and null-controllability of discrete-time linear systems](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md): $N$-step reachability of the conjugate-transposed pair, for part 2.
- [Cayley–Hamilton theorem](../../../LinearAlgebra/eigenvalues-and-canonical-forms/characteristic-polynomials-and-the-cayley-hamilt/cayley-hamilton-theorem/aeval-self-charpoly.md): the conditions $C A^k x = 0$ with $k \ge n$ follow from those with $k < n$ (part 3).

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 6.2: the matrices $O_k(A, C)$ in (6.6), Corollary 6.2.4(a) and Theorem 23 (p. 271), and the dualization remarks at the top of p. 272.
