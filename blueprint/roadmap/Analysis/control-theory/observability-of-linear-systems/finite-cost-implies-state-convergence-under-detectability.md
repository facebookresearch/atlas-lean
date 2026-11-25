# Vanishing forcing of a stable system, and finite cost under detectability

Discrete time throughout.

1. **Stable system with vanishing forcing.** If $M \in \mathbb{C}^{n \times n}$ is convergent and $x(k+1) = M x(k) + v(k)$ with $v(k) \to 0$, then $x(k) \to 0$, for every initial state $x(0)$.
2. **Finite cost implies state convergence.** Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{q \times n}$, and let $R \in \mathbb{R}^{m \times m}$ be positive definite. Suppose $(C, A)$ is detectable: some $L$ makes $A + LC$ convergent. If $x(k+1) = A x(k) + B u(k)$ and

    $$\sum_{k \ge 0} \Big( \|C x(k)\|^2 + u(k)^\top R\, u(k) \Big) < \infty ,$$

    then $x(k) \to 0$.

**Proof.**

- **Part 1.** Write $x(k) = M^k x(0) + \sum_{j < k} M^{k-1-j} v(j)$ and take $c \ge 1$, $0 \le \rho < 1$ with $\|M^i\| \le c\rho^i$. The first term tends to $0$. For the convolution, split the sum at $j = k/2$. The early terms are at most $c \sup_j \|v(j)\| \sum_{i \ge (k-1)/2} \rho^i \to 0$, and the late terms are at most $\frac{c}{1 - \rho} \sup_{j \ge k/2} \|v(j)\| \to 0$.
- **Part 2.** The summable cost gives $C x(k) \to 0$ and, because $R \succ 0$, $u(k) \to 0$. Rewrite the dynamics as $x(k+1) = (A + LC) x(k) - L\, C x(k) + B u(k)$, a convergent system with forcing $-LCx(k) + Bu(k) \to 0$, and apply part 1.

## Proof depends on

- [Exponential stability of linear difference equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-difference-equations.md): powers of a convergent matrix decay geometrically

## Background

- [Hautus test for stabilizability and detectability, discrete time](../pole-placement/hautus-test-for-stabilizability-and-detectability-discrete-time.md): a rank test for the detectability of $(C, A)$ used in part 2

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 7.3: Lemma 7.3.2 (a uniformly BIBO-stable behavior maps inputs tending to $0$ to outputs tending to $0$, p. 328), Proposition 7.3.3 (internal stability implies uniform BIBO stability, p. 328) and the observer argument in the proof of Lemma 7.3.4 (detectability: $C\xi \to 0$ implies $\xi \to 0$, p. 329).
