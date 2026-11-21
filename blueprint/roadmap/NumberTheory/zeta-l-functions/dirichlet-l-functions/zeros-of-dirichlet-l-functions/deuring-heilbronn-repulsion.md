# Deuring–Heilbronn repulsion of zeros by an exceptional zero

There are absolute constants $\varepsilon_0 > 0$ and $c > 0$ with the following property. Let
$q \ge 2$, let $\chi_1$ be a real Dirichlet character modulo $q$, and suppose that
$L(\beta, \chi_1) = 0$ with $\beta = 1 - \varepsilon / \log q$ and $0 < \varepsilon \le \varepsilon_0$.
Then every zero $\sigma + it \ne \beta$ of an L-function $L(\cdot, \chi)$, for $\chi$ a Dirichlet
character modulo $q$ (possibly $\chi_1$ or the principal character), satisfies

$$
\sigma \le 1 - c \, \frac{\log(1/\varepsilon)}{\log\bigl(q (2 + |t|)\bigr)}.
$$

An exceptional zero thus enlarges the classical zero-free region at the modulus $q$ by a factor of
order $\log(1/\varepsilon)$. The constants are effective.

The proof cited below starts from the classical zero-free region at a fixed modulus, with its
exceptional zero, and the lower bound $L(1, \chi_1) \gg q^{-1/2} \log^{-O(1)} q$ given by the class
number formula. It shows that the exceptional zero makes the non-negative multiplicative function
$1 * \chi_1$ small on average, so that $\chi_1(p) = -1$ for most primes $p$ in a range, and inserts
this weight, besides sieve weights, into zero-detecting Dirichlet polynomials.

## Proof depends on

- [Classical zero-free region for Dirichlet L-functions of a fixed modulus](dirichlet-lfunction-zero-free-region-fix.md)

## Sources

- T. Tao, *254A, Notes 7: Linnik's theorem on primes in arithmetic progressions* (2015), Theorem 9 (Deuring–Heilbronn repulsion phenomenon, in Linnik's form: if $q \ge 2$ has an exceptional zero $\beta = 1 - \varepsilon/\log q$ with $\varepsilon$ small, all other zeros $\sigma + it$ of L-functions of modulus $q$ satisfy $\sigma \le 1 - c \log(1/\varepsilon)/\log(q(2 + |t|))$, with effective constants), proved in Sections 2 and 3, <https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/>.
