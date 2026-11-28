# Interval analysis with widening and narrowing

In the interval domain, each variable is abstracted by $\bot$ or an interval $[a, b]$ with $a \le b$ in $\mathbb{Z} \cup \{-\infty, +\infty\}$, ordered by inclusion. Let $F$ be a monotone abstract functional on abstract states whose concretization over-approximates the collecting semantics. A *widening* $\nabla$ satisfies $x \sqcup y \sqsubseteq x \nabla y$, and for every sequence $(y_n)$ the sequence $x_0 = y_0$, $x_{n+1} = x_n \nabla y_{n+1}$ is eventually constant; extending unstable bounds to $\pm\infty$ is one. Starting from $X_0 = \bot$, the iteration $X_{n+1} = X_n \nabla F(X_n)$ is eventually constant at some $X^*$ with $F(X^*) \sqsubseteq X^*$, and $X^*$ is a sound over-approximation. A *narrowing* $\Delta$ satisfies $y \sqsubseteq x \,\Delta\, y \sqsubseteq x$ whenever $y \sqsubseteq x$, and decreasing iterations with it stabilize; the iteration $Y_0 = X^*$, $Y_{k+1} = Y_k \,\Delta\, F(Y_k)$ stays above the least fixed point of $F$, so it remains sound, and it is eventually constant.

## Expansion

This page becomes ready once:

- Abstract interpretation framework with collecting semantics (proof prerequisite; formal statement exists, page pending)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, 2022, <https://cs.au.dk/~amoeller/spa/>
- P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", *Proceedings of the 4th ACM POPL*, 1977
