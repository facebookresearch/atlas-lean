# Asymptotic for the divisor function summed over $B_\kappa$-free integers

Let $\kappa$ be
a function from the natural numbers to the natural numbers and let $K \ge 2$ be the minimum of
$\kappa(p)$ over the primes $p$: $\kappa(p) \ge K$ for every prime $p$, with equality for some
prime. Let $q_{B_\kappa}$ be the indicator of $B_\kappa$-free integers, $\tau(n)$ the number of
positive divisors of $n$, $\gamma$ the Euler–Mascheroni constant and
$\Delta(x) = \sum_{1 \le n \le x} \tau(n) - x \log x - (2\gamma - 1) x$ the Dirichlet divisor
error term, and put

$$C_\kappa = \prod_p \Bigl(1 - \frac{\kappa(p) + 1}{p^{\kappa(p)}} +
\frac{\kappa(p)}{p^{\kappa(p)+1}}\Bigr),$$

the product running over all primes $p$. Then there is a real constant $\beta_\kappa$ such that
$E(x) = \sum_{1 \le n \le x} q_{B_\kappa}(n) \tau(n) - C_\kappa x \log x - \beta_\kappa x$
satisfies the following as $x \to \infty$. If $K \le 3$, then $E(x) = O(x^{1/K + \varepsilon})$
for every $\varepsilon > 0$. If $K \ge 4$, then for every real $\eta \ge 1/4$ with
$\Delta(x) = O(x^\eta)$, $E(x) = O(x^{\eta + \varepsilon})$ for every $\varepsilon > 0$.

## Sources

- André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75, Corollary 2.
