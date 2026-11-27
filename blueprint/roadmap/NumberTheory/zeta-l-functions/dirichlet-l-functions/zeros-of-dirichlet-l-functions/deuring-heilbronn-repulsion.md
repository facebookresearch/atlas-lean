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

Linnik's proof starts from the classical zero-free region at a fixed modulus, with its exceptional
zero, and a lower bound for $L(1, \chi_1)$ from the class number formula. The exceptional zero
forces $\chi_1(p) = -1$ for most primes $p$ in a suitable range, and weights built from $\chi_1$,
besides sieve weights, are inserted into zero-detecting Dirichlet polynomials.

## Proof depends on

- [Classical zero-free region for Dirichlet L-functions of a fixed modulus](dirichlet-l-function-zero-free-region-fixed-modulus.md)

## Sources

- T. Tao, *254A, Notes 7: Linnik's theorem on primes in arithmetic progressions* (2015), <https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/>, Theorem 9, for the statement (Deuring–Heilbronn repulsion phenomenon, in Linnik's form: if $q \ge 2$ has an exceptional zero $\beta = 1 - \varepsilon/\log q$ with $\varepsilon$ small, all other zeros $\sigma + it$ of L-functions of modulus $q$ satisfy $\sigma \le 1 - c \log(1/\varepsilon)/\log(q(2 + |t|))$, with effective constants). The notes give an argument for it in Sections 2 and 3, following H. Iwaniec and E. Kowalski, *Analytic Number Theory*, ch. 18; in a comment of 17 March 2024 on the notes, the author records that the last step of their Proposition 23 does not handle ordinates $T$ comparable to $q^{1/\varepsilon}$, and refers readers to other treatments of Linnik's theorem.
