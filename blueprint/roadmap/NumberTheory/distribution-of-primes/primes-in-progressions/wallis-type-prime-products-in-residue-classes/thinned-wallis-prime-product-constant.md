# The constant in the thinned Wallis-type prime product asymptotic

Let $m \ge 2$, let
$q = 2^m$, and let $S$ be a set of units of $\mathbb{Z}/q\mathbb{Z}$. Let $\varphi$ be Euler's
totient function and $\chi_4$ the nontrivial Dirichlet character modulo $4$, put
$\mu(S) = \sum_{a \in S} \chi_4(a)$, where $\chi_4(a)$ means $\chi_4$ of the reduction of $a$
modulo $4$, and for real $x$ let

$$P_S(x) = \prod_{p \le x,\ p \bmod q \in S} \frac{p - \chi_4(p)}{p + \chi_4(p)},$$

the product running over primes $p$. Suppose that $C(a)$ and $D(a)$, for $a \in S$, are real
numbers with

$$C(a) = \lim_{x \to \infty} (\log x)^{1/\varphi(q)} \prod_{p \le x,\ p \equiv a \ (q)} (1 - 1/p),$$



$$D(a) = \lim_{x \to \infty} \prod_{p \le x,\ p \equiv a \ (q)} (1 - 1/p^2),$$

the products running over primes $p$. Put
$K = \prod_{a \in S} \left(C(a)^2 / D(a)\right)^{\chi_4(a)}$. Then
$P_S(x) / \left(K (\log x)^{-2\mu(S)/\varphi(q)}\right) \to 1$ as $x \to \infty$, and if
$\mu(S) = 0$ then $P_S(x) \to K$ as $x \to \infty$.

## Sources

- Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*, INTEGERS 26 (2026), Article A90, Theorem 2 (`integers-2026-A90-thm-2`).
