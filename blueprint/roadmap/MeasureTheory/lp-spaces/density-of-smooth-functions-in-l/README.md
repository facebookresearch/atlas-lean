# Density of smooth compactly supported functions in L^p

Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra, such as $\mathbb{R}^n$, let $\mu$ be a
measure on $E$ that is finite on compact sets, such as Lebesgue measure, let $F$ be a real normed space, such as
$\mathbb{C}$, and let $1 \le p < \infty$. Then the classes in $L^p(\mu; F)$ that contain an infinitely differentiable
function $E \to F$ with compact support are dense in $L^p(\mu; F)$. This is the general form of the density of
$C_c^\infty(\mathbb{R}^n)$ in $L^p(\mathbb{R}^n)$: taking $E = \mathbb{R}^n$, $\mu$ Lebesgue measure and
$F = \mathbb{C}$ gives it.

## Idea

Continuous functions with compact support are dense in $L^p$ for such a measure, which is regular: the simple functions
$\sum_j v_j \chi_{A_j}$ with vectors $v_j \in F$ and sets $A_j$ of finite measure are dense, and each $\chi_{A_j}$ is
close in $L^p$ to a continuous compactly supported real function. A continuous compactly supported $g$ is then uniformly
approximated by smooth functions supported in a fixed compact set, with no completeness of $F$ needed: for a smooth
partition of unity $(\varphi_i)$ subordinate to a cover of the support of $g$ by finitely many small balls with centres
$x_i$, the finite sum $\sum_i \varphi_i \, g(x_i)$ of smooth real functions times fixed vectors of $F$ is uniformly
close to $g$. Uniform closeness on a fixed compact set, which has finite measure, gives closeness in $L^p(\mu)$. When
$F$ is complete, as $\mathbb{C}$ is, convolving $g$ with smooth mollifiers, for a Haar measure of $E$ such as Lebesgue
measure, is the classical alternative. For Lebesgue measure on $\mathbb{R}^n$ with $n \ge 1$ the statement fails for
$p = \infty$: a limit in $L^\infty$ of continuous functions agrees almost everywhere with a continuous function, which
the indicator of a ball does not.

## Statements

- [Smooth compactly supported functions are dense in $L^p$](dense-has-compact-support-cont-diff.md)

## Background

- [L^p spaces](../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/README.md): the space $L^p$
