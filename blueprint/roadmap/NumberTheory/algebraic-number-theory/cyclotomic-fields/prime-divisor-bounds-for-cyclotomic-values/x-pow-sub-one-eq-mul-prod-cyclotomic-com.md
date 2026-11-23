# Factorization into composed cyclotomic polynomials

Let $x$ be the indeterminate of the
polynomial ring $\mathbb{Z}[x]$. Let $m$ be a natural number, let $p_1, \dots, p_m$ be primes,
not necessarily distinct, let $a_1, \dots, a_m$ be natural numbers, and put
$n = \prod_{i=1}^m p_i^{a_i}$. For $1 \le i \le m$ let $x_i = x^{N_i}$ with
$N_i = \prod_{1 \le r < i} p_r^{a_r}$. Then

$$x^n - 1 = (x - 1) \prod_{i=1}^m \prod_{j=1}^{a_i} \Phi_{p_i}(x_i^{p_i^{j-1}}),$$

where $\Phi_p$ is the $p$-th cyclotomic polynomial over $\mathbb{Z}$ and $\Phi_{p_i}(\cdot)$
denotes composition of polynomials.

The source takes the prime factorization of $n$; the identity needs only that each $p_i$ is
prime. The definition of $x_i$ follows the arXiv version of the source (arXiv:2412.00010),
which the journal statement refers to as "$x_k$ as above".

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Proposition 4.
