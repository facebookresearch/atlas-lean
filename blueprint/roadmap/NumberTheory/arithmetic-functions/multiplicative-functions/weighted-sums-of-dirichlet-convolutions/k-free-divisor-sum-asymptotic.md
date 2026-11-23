# Asymptotic for the divisor function summed over $k$-free integers

Let $k \ge 2$ be a
natural number, let $q_k$ be the indicator of $k$-free integers (the indicator of
$B_\kappa$-free integers for the constant function $\kappa = k$), let $\tau(n)$ be the number of
positive divisors of $n$, let $\gamma$ be the Euler–Mascheroni constant, let
$\Delta(x) = \sum_{1 \le n \le x} \tau(n) - x \log x - (2\gamma - 1) x$ be the Dirichlet divisor
error term, and put

$$c_k = \prod_p \Bigl(1 - \frac{k + 1}{p^k} + \frac{k}{p^{k+1}}\Bigr),$$

the product running over all primes $p$. Then there is a real constant $\beta_k$ such that
$E(x) = \sum_{1 \le n \le x} q_k(n) \tau(n) - c_k x \log x - \beta_k x$ satisfies the following
as $x \to \infty$. If $k \le 3$, then $E(x) = O(x^{1/k + \varepsilon})$ for every
$\varepsilon > 0$. If $k \ge 4$, then for every real $\eta \ge 1/4$ with $\Delta(x) = O(x^\eta)$,
$E(x) = O(x^{\eta + \varepsilon})$ for every $\varepsilon > 0$.

## Sources

- André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75, Corollary 1.
