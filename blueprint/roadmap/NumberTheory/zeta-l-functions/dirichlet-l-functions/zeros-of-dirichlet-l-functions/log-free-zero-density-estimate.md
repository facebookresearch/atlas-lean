# Log-free zero-density estimate for Dirichlet L-functions

For an integer $q \ge 2$, a real $T > 1$ and $1/2 \le \alpha \le 1$, let $N(\alpha, q, T)$ be the
number of zeros $\sigma + it$, counted with multiplicity, of the L-functions $L(\cdot, \chi)$ of the
Dirichlet characters $\chi$ modulo $q$ with $\sigma \ge \alpha$ and $0 \le t \le T$. There is an
absolute constant $C$ such that

$$
N(\alpha, q, T) \le C (qT)^{C(1 - \alpha)}
$$

for all such $q$, $T$ and $\alpha$, with $C$ effective. Compared with density estimates of the
form $N(\alpha, q, T) \ll (qT)^{A(1-\alpha)} \log^{B}(qT)$, the bound has no logarithmic factor,
which matters for $\alpha$ within $O(1/\log(qT))$ of $1$.

The proof cited below may assume $T \ge q^{10}$ and $\alpha = 1 - A/\log T$ with
$A = O(\log \log T)$, the other range following from a density estimate with logarithmic losses.
It handles the principal character, whose L-function has the zeros of $\zeta$ in
$\operatorname{Re} s > 0$, with zero-free regions for $\zeta$: the Vinogradov–Korobov region for
large ordinates and the classical region for bounded ones. The other characters are handled with
zero-detecting Dirichlet polynomials weighted by Selberg sieve weights, which concentrate them on
almost primes.

## Proof depends on

- [Vinogradov–Korobov zero-free region](../../../arithmetic-functions/special-integer-classes/mean-value-of-2-n-over-squareful-numbers/zeta-ne-zero-vinogradov-korobov.md)
- [Classical zero-free region for the Riemann zeta function](../../riemann-zeta/zero-free-regions-for-the-riemann-zeta-function/riemann-zeta-ne-zero-of-classical-zero-f.md)

## Sources

- T. Tao, *254A, Notes 7: Linnik's theorem on primes in arithmetic progressions* (2015), Theorem 7 (log-free grand density estimate: $N(\alpha, q, T) \ll (qT)^{O(1-\alpha)}$ for $q, T > 1$ and $1/2 \le \alpha \le 1$, with effective implied constants; $N(\alpha, q, T)$ as defined before it, with $0 \le t \le T$ by conjugation symmetry) and its proof in Section 1, <https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/>.
