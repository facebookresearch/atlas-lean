# The $B_\kappa$-free indicator twisted by the principal character, convolved with $\mu$

Let $\kappa$ be a function from the natural numbers to the natural numbers with $\kappa(p) \ge 1$
for every prime $p$, let $\xi$ be a natural number, let $q_{B_\kappa}$ be the indicator of
$B_\kappa$-free integers and let $\mu$ be the Möbius function. Put $w(d) = q_{B_\kappa}(d)$ if
$\gcd(d, \xi) = 1$ and $w(d) = 0$ otherwise, so that $w = q_{B_\kappa} \chi_\xi$ with $\chi_\xi$
the principal character modulo $\xi$, and let $(w * \mu)(n) = \sum_{d \mid n} w(d) \mu(n/d)$, the
sum running over the positive divisors $d$ of $n$ (it is empty for $n = 0$). For $r \ge 1$ with
prime factorization $r = \prod_p p^{e_p}$ write $r^\kappa = \prod_p p^{\kappa(p) e_p}$, and set
$0^\kappa = 1$. Then for every natural number $n$ with $(w * \mu)(n) \ne 0$ there are natural
numbers $\ell$ and $r$ with $\ell \mid \xi$, $\gcd(r, \xi) = 1$ and $n = \ell r^\kappa$. Moreover,
for all natural numbers $\ell$ and $r$ with $\ell \mid \xi$, $\gcd(r, \xi) = 1$ and $r \ge 1$,
$(w * \mu)(\ell r^\kappa) = \mu(\ell) \mu(r)$.

The hypothesis $r \ge 1$ in the evaluation is needed: for $r = 0$ the formula is false. No
positivity of $\xi$ is assumed.

## Sources

- André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75, Lemma 6, Equation (23).
