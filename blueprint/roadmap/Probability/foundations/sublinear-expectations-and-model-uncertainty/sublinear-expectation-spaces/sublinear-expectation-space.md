# Sublinear expectation space

A sublinear expectation space $(\Omega, \mathcal{H}, \mathbb{E})$ consists of a set $\Omega$, a
set $\mathcal{H}$ of real functions on $\Omega$ and a functional $\mathbb{E}$ on real functions on
$\Omega$ such that: for every $n$, all $X_1, \dots, X_n \in \mathcal{H}$ and every
$\varphi \in C_{l.Lip}(\mathbb{R}^n)$ ([Peng's test functions](is-loc-lip.md)),
$\varphi(X_1, \dots, X_n) \in \mathcal{H}$ (so $\mathcal{H}$ is a linear space containing the
constants and $|X|$ for each of its elements); and $\mathbb{E}$ is monotone, constant preserving,
subadditive and positively homogeneous on $\mathcal{H}$, as for a [sublinear
expectation](../sublinear-expectations/is-sublinear-expectation.md). Only the values of $\mathbb{E}$ on $\mathcal{H}$ are
constrained.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010, Chapter I, Definition 1.1 with the standing convention of Section 1.
