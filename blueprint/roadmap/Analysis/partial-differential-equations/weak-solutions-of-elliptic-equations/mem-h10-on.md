# Sobolev space $H^1_0(U)$

A function $u \in H^1(U)$ belongs to $H^1_0(U)$ when there are test functions
$\varphi_k \in C^\infty_c(U)$ with $\varphi_k \to u$ and $\partial_i \varphi_k \to \partial_i u$ in
$L^2(U)$ for every $i$: $H^1_0(U)$ is the closure of $C^\infty_c(U)$ in the $H^1(U)$ norm, the space
that encodes the Dirichlet condition $u = 0$ on $\partial U$. For sufficiently regular boundaries it
coincides with the functions whose trace is zero (Hunter proves this for the half-space); for an
arbitrary open $U$ no trace operator is assumed, and the definition is the closure.

## Background

- [Test function on an open set](is-test-function-on.md) and
  [weak partial derivative on an open set](is-weak-partial-deriv-on.md).

## Sources

- J. K. Hunter, *Notes on Partial Differential Equations*, UC Davis, [Chapter 3 (Sobolev spaces)](https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf), §3.6 (remark after Theorem 3.24: the closure of $C^\infty_c(\Omega)$ in $W^{k,p}(\Omega)$
  is $W^{k,p}_0(\Omega)$), Definition 3.43 and Theorem 3.44 (the half-space and the trace
  characterisation).
