# Truncated generating function for $\ell$-regular overpartitions

Let $\ell \ge 1$, $N$ and
$n \le N$ be natural numbers, and let $A_\ell(n)$ be the number of overpartitions of $n$ with no
part divisible by $\ell$. Then the coefficient of $X^n$ in the polynomial

$$\prod_{1 \le k \le N,\ \ell \nmid k} \Big((1 + X^k) \sum_{i=0}^{N} X^{ki}\Big) \in \mathbb{N}[X]$$

equals $A_\ell(n)$.

This is a finite-polynomial form of the generating function
$\sum_{n \ge 0} A_\ell(n) q^n = \prod_{k \ge 1,\ \ell \nmid k} (1 + q^k)/(1 - q^k)$: each
geometric series is cut off at $i = N$, and only coefficients up to degree $N$ are compared.

## Sources

- Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*, INTEGERS 25 (2025), Article A3, Identity (1).
