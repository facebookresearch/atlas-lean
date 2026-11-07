# Asymptotic count of primes with more than $\ell$ representations

For every natural
number $\ell$ and every $\varepsilon > 0$ there is a natural number $C$ such that the following
holds for all coprime natural numbers $c$ and $d$ with $C \le c < d$. Put
$g_\ell(c, d) = (\ell + 1)cd - c - d$, and let $\pi_{\ell,c,d}$ be the number of primes
$n \le g_\ell(c, d)$ such that the equation $n = cx + dy$ has more than $\ell$ solutions
$(x, y)$ in natural numbers. Then, with $\pi$ the prime-counting function,

$$
\left|\pi_{\ell,c,d} - \frac{\pi(g_\ell(c, d))}{2\ell + 2}\right| <
\varepsilon \, \frac{\pi(g_\ell(c, d))}{2\ell + 2}.
$$

That is, $\pi_{\ell,c,d} \sim \pi(g_\ell(c, d))/(2\ell + 2)$ as $c \to \infty$, uniformly over
coprime $d > c$.

## Sources

- Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and Skałba, III*, INTEGERS 25 (2025), Article A51, Theorem 1, with `g_ℓ(c, d)` from equation (1).
