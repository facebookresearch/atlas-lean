# Asymptotic for the divisor function summed over $B_\kappa$-free integers in a progression

Let $\kappa$ be a function from the natural numbers to the natural numbers and let $K$ be the
minimum of $\kappa(p)$ over the primes $p$: $\kappa(p) \ge K$ for every prime $p$, with equality
for some prime. Assume $K \ge 2$ and $K \ne 3$. Let $a$ and $\xi$ be natural numbers with
$a < \xi$ and $\gcd(a, \xi) = 1$. Let $q_{B_\kappa}$ be the indicator of $B_\kappa$-free
integers, $\tau(n)$ the number of positive divisors of $n$ and $\varphi$ Euler's totient
function, and put

$$C_{\kappa,\xi} = \prod_{p \nmid \xi} \Bigl(1 - \frac{\kappa(p) + 1}{p^{\kappa(p)}} +
\frac{\kappa(p)}{p^{\kappa(p)+1}}\Bigr),$$

the product running over the primes $p$ that do not divide $\xi$. Let $\eta = 1/2$ if $K = 2$
and $\eta = 1/3$ if $K \ge 4$. Then there is a real constant $\tilde c$ such that for every
$\varepsilon > 0$, as $x \to \infty$,

$$\sum_{\substack{1 \le n \le x \\ n \equiv a \pmod{\xi}}} q_{B_\kappa}(n) \tau(n) =
\frac{\varphi(\xi)}{\xi^2} C_{\kappa,\xi} \, x \log x + \tilde c x + O(x^{\eta + \varepsilon}).$$

The case $K = 3$ is not covered by the paper's statement and is excluded.

## Sources

- André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75, Corollary 3, Equation (15) (`integers-2024-A75-cor-3`).
