# Sublinear expectation spaces

A sublinear expectation space $(\Omega, \mathcal{H}, \mathbb{E})$ consists of a set $\Omega$, a set $\mathcal{H}$ of real functions on $\Omega$, and a functional $\mathbb{E}$ on real functions on $\Omega$ such that: for every $n$, all $X_1, \dots, X_n \in \mathcal{H}$ and every $\varphi : \mathbb{R}^n \to \mathbb{R}$ in Peng's class $C_{l.Lip}(\mathbb{R}^n)$, that is, with $|\varphi(x) - \varphi(y)| \le C (1 + \|x\|^m + \|y\|^m) \|x - y\|$ for some constants $C$ and $m \in \mathbb{N}$, the function $\varphi(X_1, \dots, X_n)$ belongs to $\mathcal{H}$; and $\mathbb{E}$ is monotone, constant preserving, subadditive and positively homogeneous on $\mathcal{H}$, as for a sublinear expectation. In particular $\mathcal{H}$ is a linear space containing the constants and $|X|$ for each of its elements. Only the values of $\mathbb{E}$ on $\mathcal{H}$ are constrained.

## Idea

This is the setting of Peng's theory of nonlinear expectations, the analogue of a probability space when the law is uncertain. Closure under the test functions $C_{l.Lip}$ lets one speak of the distribution of a random vector $X$ through the values $\mathbb{E}[\varphi(X)]$: two vectors are identically distributed when these values agree for every test function. Independence is defined by iterated evaluation: $Y$ is independent from $X$ if $\mathbb{E}[\varphi(X, Y)] = \mathbb{E}\bigl[\mathbb{E}[\varphi(x, Y)]_{x = X}\bigr]$ for every test function. Unlike classical independence, this relation is not symmetric in $X$ and $Y$. The axioms already give cash translatability, $\mathbb{E}[c + X] = c + \mathbb{E}[X]$. These notions are the ingredients of the G-normal law and of Peng's law of large numbers and central limit theorem.

## Statements

- [Sublinear expectation space](sublinear-expectation-space.md)
- [Peng's test-function class $C_{l.Lip}$](is-loc-lip.md): definition used in the main definition
- [Constants are test functions](is-loc-lip-const.md): basic property of the test functions
- [Lipschitz functions are test functions](is-loc-lip-of-lipschitz-with.md): basic property of the test functions
- [Constants are random variables](const-mem.md): basic property: constants are random variables
- [Sums of random variables](add-mem.md): basic property: sums of random variables
- [Cash translatability](expectation-const-add.md): basic property: cash translatability
- [Identically distributed random vectors](ident-distrib.md): definition of identical distribution in this framework
- [Independence under a sublinear expectation](indep-from.md): definition of independence in this framework

## Background

- [Sublinear expectations and their representation](../sublinear-expectations/README.md)

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*, arXiv:1002.4546, 2010.
