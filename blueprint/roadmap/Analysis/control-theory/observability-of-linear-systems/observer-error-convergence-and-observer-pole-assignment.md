# Observer error convergence and observer pole assignment

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$ and $D \in \mathbb{R}^{p \times m}$, and consider the plant $\dot x = A x + B u$, $y = C x + D u$ in continuous time, or $x(k+1) = A x(k) + B u(k)$, $y(k) = C x(k) + D u(k)$ in discrete time. Let $L \in \mathbb{R}^{n \times p}$ and run the observer

$$\dot z = (A + LC) z + B u - L (y - D u) \qquad \bigl(\text{resp. } z(k+1) = (A + LC) z(k) + B u(k) - L (y(k) - D u(k))\bigr),$$

driven by the same known input $u$ and the measured output $y$, with the same $D$ as the plant.

1. **Error dynamics.** For every initial plant state, every initial observer state and every input, the error $e = z - x$ satisfies $\dot e = (A + LC) e$ (resp. $e(k+1) = (A + LC) e(k)$).
2. **Convergence.** If $A + LC$ is Hurwitz (resp. convergent), there are $M > 0$ and $\alpha > 0$ (resp. $0 \le r < 1$) with $\|e(t)\| \le M e^{-\alpha t} \|e(0)\|$ for $t \ge 0$ (resp. $\|e(k)\| \le M r^k \|e(0)\|$), whatever the input.
3. **Observer pole assignment.** Suppose $p = 1$ and that $(A, C)$ is observable, that is, the $n \times n$ matrix with rows $C, CA, \dots, CA^{n-1}$ has rank $n$. Then for every monic real polynomial $q$ of degree $n$ there is $L \in \mathbb{R}^{n \times 1}$ with $\det(sI - A - LC) = q(s)$.

Part 3 is the pole-shifting theorem applied to the pair $(A^\top, C^\top)$, which satisfies the Kalman rank condition exactly when $(A, C)$ is observable, followed by transposition ($L = K^\top$). Choosing $q$ with all roots in the open left half-plane (resp. open unit disc) makes the error decay as in part 2.

## Depends on

- [Observability of discrete-time linear systems over a finite horizon](observability-rank-condition-discrete-time.md): the rank condition on $C, CA, \dots, CA^{n-1}$ is observability

## Proof depends on

- [Pole-shifting theorem](../pole-placement/exists-charpoly-add-comp-eq.md): applied to $(A^\top, C^\top)$ for part 3
- [Exponential stability of linear differential equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md): decay of the error for a Hurwitz $A + LC$
- [Exponential stability of linear difference equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-difference-equations.md): decay of the error for a convergent $A + LC$

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 7.1: the observer (7.3) and its error equation in the proof of Theorem 31 (p. 319); pole assignment by duality from the Pole-Shifting Theorem, Theorem 13 (p. 186), and observability of $(A, C)$ as controllability of $(A^\top, C^\top)$, Theorems 23 and 24 (p. 271).
