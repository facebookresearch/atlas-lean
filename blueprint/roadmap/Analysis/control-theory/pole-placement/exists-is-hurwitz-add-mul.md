# Controllable linear systems have a Hurwitz closed loop

Let $A \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{R}^{n \times m}$ satisfy the Kalman rank condition $\operatorname{Span} \{ A^i B u : u \in \mathbb{R}^m, \ 0 \le i < n \} = \mathbb{R}^n$. Then there is $K \in \mathbb{R}^{m \times n}$ such that $A + BK$ has characteristic polynomial $(X + 1)^n$; in particular every complex eigenvalue of $A + BK$ equals $-1$, so $A + BK$ is Hurwitz.

This is the first step of Coron, *Control and Nonlinearity* (AMS 2007), Corollary 10.12, which Coron derives from the pole-shifting theorem and Theorem 10.9. For example, it stabilises the unstable scalar system $\dot x = x + u$.

## Informally uses

- [Pole-shifting theorem](exists-charpoly-add-comp-eq.md): assigns the polynomial $(X + 1)^n$.
