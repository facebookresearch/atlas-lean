# Asymptotic for thinned Wallis-type prime products

Let $m \ge 2$, let $q = 2^m$, and let
$S$ be a set of units of $\mathbb{Z}/q\mathbb{Z}$. Let $\varphi$ be Euler's totient function and
$\chi_4$ the nontrivial Dirichlet character modulo $4$, put $\mu(S) = \sum_{a \in S} \chi_4(a)$,
where $\chi_4(a)$ means $\chi_4$ of the reduction of $a$ modulo $4$, and for real $x$ let

$$P_S(x) = \prod_{p \le x,\ p \bmod q \in S} \frac{p - \chi_4(p)}{p + \chi_4(p)},$$

the product running over primes $p$. Then there is a real number $K > 0$ such that
$P_S(x) / \left(K (\log x)^{-2\mu(S)/\varphi(q)}\right) \to 1$ as $x \to \infty$.

## Sources

- Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*, INTEGERS 26 (2026), Article A90, Theorem 1.
