# Vishwakarma–Singh congruence for ordered partitions into multiples

Let $p$ be an odd
prime and let $a, k, s, t$ be positive integers with $\gcd(a, p - 1) = 1$, $s \le p - 2$ and
$k \equiv 1 \pmod{p(p-1)}$, such that $p^2 \mid k - 1$ whenever $p - 1 \mid t$. Let
$\mu = \lfloor aks/(p - 1) \rfloor$. Then

$$\sum_{j=1}^{\mu} \sum_{\omega} (\omega_1 \cdots \omega_s)^t \equiv 0 \pmod{p},$$

where for each $j$ the inner sum runs over all $s$-tuples $\omega = (\omega_1, \dots, \omega_s)$
with entries in $\{an : 1 \le n \le k\}$ and $\omega_1 + \cdots + \omega_s = j(p - 1)$.

The source states this with two differences. It assumes $s \not\equiv 0 \pmod{p}$ in place of
$s \le p - 2$; with that hypothesis the claim fails, e.g. for $a = 1$, $p = 3$, $k = 7$, $s = 2$,
$t = 1$. It takes $\mu = \lfloor ks/(p - 1) \rfloor$; with that bound the claim fails for $a > 1$,
e.g. for $p = 5$, $a = 3$, $k = 21$, $s = t = 1$ the sum is $12$. The bound
$\lfloor aks/(p - 1) \rfloor$ covers every multiple of $p - 1$ up to $aks$, the degree of the
$s$-th power of $\sum_{n=1}^{k} (an)^t X^{an}$, to which the proof applies Hermite's criterion.

## Sources

- Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 4 (`integers-2024-A12-cor-4`).
