# Zero-order-hold sampling of a linear time-invariant system

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$ and $\delta > 0$, and let $(u_k)_{k \ge 0}$ be inputs in $\mathbb{K}^m$. Let $x$ be continuous on $[0, \infty)$ and, on each interval $[k\delta, (k+1)\delta]$, differentiable (one-sidedly at the endpoints) with $\dot x(t) = A x(t) + B u_k$; that is, $x$ is the state of $\dot x = A x + B u$ under the held input $u(t) = u_k$ for $t \in [k\delta, (k+1)\delta)$. Let

$$F = e^{\delta A}, \qquad A^{(\delta)} = \int_0^\delta e^{(\delta - s)A} \, ds = \int_0^\delta e^{sA} \, ds, \qquad G = A^{(\delta)} B .$$

Then:

1. the samples $x_k = x(k\delta)$ satisfy $x_{k+1} = F x_k + G u_k$ for every $k \ge 0$;
2. $A A^{(\delta)} = e^{\delta A} - I$;
3. if $A = 0$ then $G = \delta B$;
4. if $A$ is invertible then $G = A^{-1} (e^{\delta A} - I) B$.

Part 1 is Duhamel's formula with the constant forcing $B u_k$, started at time $k\delta$; on $[k\delta, (k+1)\delta]$ the state agrees with that solution, because $e^{-tA}$ times their difference has zero derivative there. Part 2 holds because $A^{(\delta)} = f(A)$ for the entire function $f(s) = \sum_{j \ge 0} \frac{\delta^{j+1}}{(j+1)!} s^j$, which satisfies $s f(s) = e^{\delta s} - 1$ and $f(0) = \delta$; parts 3 and 4 follow.

## Proof depends on

- [Duhamel's formula (variation of constants)](../../ordinary-differential-equations/duhamel-variation-of-constants.md): the state at the end of each sampling interval (part 1).

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 2.10, Definition 2.10.1 (p. 72), and Section 3.4: formula (3.10), the series for $A^{(\delta)}$ and the identity $A A^{(\delta)} = e^{\delta A} - I$ (pp. 99–100).
