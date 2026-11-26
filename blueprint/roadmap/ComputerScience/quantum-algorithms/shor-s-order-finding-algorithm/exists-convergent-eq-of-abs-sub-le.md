# Continued fractions recover the fraction in Shor's algorithm

Let $\xi$ be a real number and let $q$ and $n$ be natural numbers with $n^2 \le q$. If an
integer $d$ and a natural number $r$ with $0 < r < n$ satisfy $|\xi - d/r| \le 1/(2q)$, then
the rational number $d/r$ is a convergent of the continued fraction expansion of $\xi$.

In Shor's algorithm $\xi = c/q$, so $d/r$, in lowest terms, is found among the convergents of
$c/q$, which the continued fraction algorithm computes in polynomial time. The proof applies
Legendre's theorem on rational approximation (if
$|\xi - p| < 1/(2 b^2)$ for a rational $p$ with reduced denominator $b$, then $p$ is a
convergent of $\xi$). The reduced denominator $b$ of $d/r$ is at most $r$, and
$1/(2q) \le 1/(2n^2) < 1/(2r^2) \le 1/(2b^2)$.

The convergent gives $d/r$ in lowest terms, hence $r$ itself only when $\gcd(d, r) = 1$. Shor
counts the outcomes with $d$ coprime to $r$, which occur with probability at least
$\varphi(r)/(3r)$ for large $n$, and repeats the experiment $O(\log \log r)$ times (Section 5,
p. 19 of the arXiv version).

## Background

- [Continued fractions and expansions of reals](../../../NumberTheory/continued-fractions-expansions/README.md): context on convergents of real numbers.

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509, arXiv:quant-ph/9508027, Section 5, the paragraph after equation (5.13).
