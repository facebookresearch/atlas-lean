# Weisner's theorem

Let $L$ be a finite lattice with least element $\hat 0$ and greatest element $\hat 1$, and let
$a \in L$ with $a \ne \hat 1$. Then

$$\sum_{t \,:\, t \wedge a = \hat 0} \mu(t, \hat 1) = 0.$$

It is a recurrence for $\mu(\cdot, \hat 1)$ with, in general, far fewer terms than the defining
one. The proof writes the indicator of $t \wedge a = \hat 0$ as
$\sum_{\hat 0 \le s \le t \wedge a} \mu(\hat 0, s)$ and exchanges the sums.

## Informally uses

- [Möbius algebra product](../../../Combinatorics/partially-ordered-sets/m-bius-algebras-and-flag-vectors/moebius-algebra-mul.md):
  Stanley's proof computes $a\,\delta_{\hat 1}$ in two ways in the Möbius algebra $A(L, K)$, using
  the basis $\delta_t = \sum_{s \le t} \mu(s, t)\, s$ of Theorem 3.9.2.

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Corollary 3.9.3.
