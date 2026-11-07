# Erdős Problem 690 is false

There is a natural number $k \ge 1$ such that the $k$-th
prime-factor density $d_k$ is not unimodal on the primes, that is, there is no prime $p_0$ such
that $d_k(p) \le d_k(q)$ for all primes $p$ and $q$ with $p \le q \le p_0$ and
$d_k(q) \le d_k(p)$ for all primes $p$ and $q$ with $p_0 \le p \le q$. Here $d_k(p)$ is the
natural density of the set of natural numbers whose $k$-th smallest prime factor is $p$ (an
unspecified real number if this density does not exist).

Cambie (Theorem 5) proves that $d_k$ is unimodal for $k = 1, 2, 3$ and not unimodal for
$4 \le k \le 20$; for example $d_4(13) = 31/5005 > d_4(17) = 206/36465 < d_4(19) = 1308/230945$.

## Sources

- S. Cambie, Resolution of Erdős' problems about unimodularity, arXiv preprint (2025), arXiv:2501.10333, https://arxiv.org/abs/2501.10333. Moved from `OpenConjectures/NumberTheory/ErdosProblem690`.
