# Helly's selection theorem

Let $(F_n)_{n \in \mathbb{N}}$ be a sequence of distribution functions on $\mathbb{R}$ (nondecreasing, right-continuous, tending to $0$ at $-\infty$ and to $1$ at $+\infty$). Then there are a subsequence $(F_{n_k})$ and a nondecreasing, right-continuous function $G : \mathbb{R} \to \mathbb{R}$ such that $F_{n_k}(x) \to G(x)$ at every point $x$ where $G$ is continuous. The limit $G$ need not be a distribution function.

## Idea

This is a compactness statement for distribution functions. The proof is a diagonal argument: the values $F_n(q)$ lie in $[0, 1]$, so one subsequence converges at every rational $q$; setting $G(x) = \inf_{q > x} \lim_k F_{n_k}(q)$ gives a nondecreasing right-continuous function, and monotonicity of the $F_n$ yields convergence at each continuity point of $G$. Mass can escape: the distribution functions of the point masses at $n$ converge to $0$ everywhere, so $G = 0$. When the sequence is tight, no mass escapes, $G$ is a distribution function, and the subsequence converges weakly; this is how Prokhorov's theorem on the real line is proved.

## Statements

- [Helly's selection theorem](helly-selection.md)
- [Distribution function](is-distribution-function.md): definition used in the main statement
- [Distribution functions are nonnegative](nonneg.md): basic property of distribution functions, used in the proof
- [Distribution functions are at most one](le-one.md): basic property of distribution functions, used in the proof
- [Distribution functions take values in the unit interval](mem-icc.md): basic property of distribution functions

## Background

- [Atoms and continuity points of a distribution function](../../distributions/distribution-functions/cumulative-distribution-function/README.md)
