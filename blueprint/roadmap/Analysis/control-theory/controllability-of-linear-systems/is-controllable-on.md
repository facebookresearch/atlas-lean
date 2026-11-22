# Controllability of a linear control system

Let $E$ and $U$ be real inner product spaces, $A : E \to E$ and $B : U \to E$ bounded linear maps, and $T \in \mathbb{R}$. The system $\dot x = A x + B u$ is **controllable on $[0, T]$** if for all $x_0, x_1 \in E$ there are a continuous control $u : \mathbb{R} \to U$ and a solution $x : \mathbb{R} \to E$ of $\dot x(t) = A x(t) + B u(t)$ with $x(0) = x_0$ and $x(T) = x_1$.

For finite-dimensional $E$ and $U$ this is Coron, *Control and Nonlinearity* (AMS 2007), Definition 1.2, on the interval $[T_0, T_1] = [0, T]$ for a time-invariant system, with continuous controls instead of $L^\infty$ controls. The two notions agree for $T > 0$: if the system is controllable with $L^\infty$ controls, its Gramian is invertible by Coron's Theorem 1.11, and the [Gramian criterion](is-controllable-on-iff-bijective-gramian.md) then gives continuous steering controls; conversely, continuous controls on $[0, T]$ are $L^\infty$ (compare Coron's Remark 1.3, which treats $L^2$ and $L^1$ controls). The criteria assume $T > 0$: at $T = 0$ a system with nonzero state space is never controllable, since $x(0) = x_0$ and $x(T) = x_1$ force $x_0 = x_1$.

## Background

- [Duhamel's formula](../../ordinary-differential-equations/duhamel-variation-of-constants.md): when $E$ is complete (for instance finite-dimensional), every continuous control has a unique solution from each initial state, given by the variation of constants formula.
