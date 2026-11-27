# Lyapunov, asymptotic and bounded-input bounded-output stability of linear systems

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$ and $D \in \mathbb{R}^{p \times m}$, with Euclidean norms on vectors and the induced operator norms on matrices. For the continuous-time system $\dot x = Ax + Bu$, $y = Cx + Du$, call the matrix $A$

- **Lyapunov stable** if $\sup_{t \ge 0} \|e^{tA}\| < \infty$, equivalently every solution of $\dot x = Ax$ is bounded on $[0, \infty)$;
- **asymptotically stable** if $e^{tA} x_0 \to 0$ as $t \to \infty$ for every $x_0$;
- **exponentially stable** if there are $M, c > 0$ with $\|e^{tA}\| \le M e^{-ct}$ for every $t \ge 0$;

and call the system **bounded-input bounded-output stable** if there is $\gamma$ such that, from $x(0) = 0$, every continuous bounded input $u$ on $[0, \infty)$ gives $\sup_{t \ge 0} \|y(t)\| \le \gamma \sup_{t \ge 0} \|u(t)\|$. Then:

1. Asymptotic and exponential stability are equivalent, and both hold exactly when $A$ is Hurwitz.
2. Asymptotic stability implies Lyapunov stability, but not conversely: $A = 0 \in \mathbb{R}^{1 \times 1}$ is Lyapunov stable and not asymptotically stable. Eigenvalues with nonpositive real parts do not suffice for Lyapunov stability: for $A = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$, $e^{tA} = \begin{pmatrix} 1 & t \\ 0 & 1 \end{pmatrix}$ is unbounded.
3. If $A$ is exponentially stable, the system is bounded-input bounded-output stable for every $B$, $C$ and $D$, with $\gamma = \|C\|\,\|B\|\,M/c + \|D\|$. The converse fails without controllability and observability: for $A = \operatorname{diag}(1, -1)$, $B = (0, 1)^\top$, $C = (0, 1)$ and $D = 0$ with scalar input $u$ the output from $x(0) = 0$ is $y(t) = \int_0^t e^{-(t - s)} u(s)\, ds$, so $\gamma = 1$ works, while $A$ is not Hurwitz.
4. **Finite horizons carry no stability information.** For every $A$, $B$, $C$, $D$, every $T > 0$, every initial state $x_0$ and every input $u$ continuous on $[0, T]$, the output is bounded on $[0, T]$ by $\|C\| K_T (\|x_0\| + T \|B\| \|u\|_\infty) + \|D\| \|u\|_\infty$, where $K_T = \max_{0 \le t \le T} \|e^{tA}\|$; for instance $A = 1$ satisfies this on every finite horizon and is not Lyapunov stable.

The same statements hold in discrete time, $x(k + 1) = Ax(k) + Bu(k)$, with $A^k$ in place of $e^{tA}$, convergent matrices (all eigenvalues of modulus less than $1$) in place of Hurwitz ones, geometric bounds $\|A^k\| \le M r^k$ with $0 \le r < 1$ in place of exponential ones and $\gamma = \|C\|\,\|B\|\,M/(1 - r) + \|D\|$; the witnesses are $A = 1$ for part 2, $A = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ with $A^k = \begin{pmatrix} 1 & k \\ 0 & 1 \end{pmatrix}$, and $A = \operatorname{diag}(2, 1/2)$ with the same $B$ and $C$ for part 3.

**Proof.** Part 1 is the equivalence of decay, exponential bounds and the Hurwitz property for $\dot x = Ax$. In part 2, an exponential bound is in particular a uniform bound; the two witnesses are direct computations. The equivalence in the definition of Lyapunov stability holds because $e^{tA} x_0$ is the solution from $x_0$: a uniform operator bound bounds every solution, and conversely, if the solutions from the basis vectors $e_1, \dots, e_n$ are bounded by $K_1, \dots, K_n$, then $\|e^{tA}\| \le \sum_j K_j$. For part 3, the output from $x(0) = 0$ is $y(t) = \int_0^t C e^{(t - s)A} B u(s)\, ds + D u(t)$, so $\|y(t)\| \le \big(\|C\|\,\|B\| \int_0^\infty M e^{-cs}\, ds + \|D\|\big) \|u\|_\infty$; in the witness the second coordinate obeys $\dot x_2 = -x_2 + u$ and the first stays $0$. Part 4 is the same estimate on $[0, T]$ with $x(t) = e^{tA} x_0 + \int_0^t e^{(t - s)A} B u(s)\, ds$ and $\|e^{(t - s)A}\| \le K_T$. The discrete-time proofs replace integrals by finite sums and $\int_0^\infty M e^{-cs}\, ds$ by $\sum_{k \ge 0} M r^k$.

## Proof depends on

- [Exponential stability of linear differential equations](asymptotic-stability-linear-differential-equations.md): part 1 in continuous time
- [Exponential stability of linear difference equations](asymptotic-stability-linear-difference-equations.md): part 1 in discrete time

## Background

- [Internal and external stability of minimal realizations](../../control-theory/realization-theory/internal-and-external-stability-of-minimal-realizations.md): bounded-input bounded-output stability is equivalent to integrability of the impulse response, and for controllable and observable systems to internal stability

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 5.5, Proposition 5.5.5 (pp. 212–213): local and global asymptotic stability of $\dot x = Ax$ are equivalent to $A$ being Hurwitz, with the uniform bound $\|e^{tA}\| \le K$ in its proof, and the discrete-time analogue; Section 7.3, the definition of uniform bounded-input bounded-output stability (p. 327) and Proposition 7.3.3 (p. 328), internal stability implies it. The witnesses, the explicit gains and the finite-horizon bound are derived on the page.
