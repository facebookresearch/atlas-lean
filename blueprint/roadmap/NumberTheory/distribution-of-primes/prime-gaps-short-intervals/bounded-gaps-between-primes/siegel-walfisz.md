# Siegel–Walfisz hypothesis for a family of sequences

Let $(\beta_x)_{x \in \mathbb{R}}$
be a family of finitely supported sequences $\beta_x : \mathbb{N} \to \mathbb{R}$ and let
$M : \mathbb{R} \to \mathbb{R}$. The family satisfies the Siegel–Walfisz hypothesis at scale $M$
if for every real $A \ge 1$ there are a real number $C > 0$ and a natural number $k$ such that,
for all sufficiently large real $x$ and all natural numbers $q \ge 1$, $r \ge 1$ and $a$ with
$\gcd(a, q) = 1$,

$$|\Delta(\beta_x^{(r)}; a \bmod q)| \le C \, \tau(qr)^k \, M(x) / (\log x)^A.$$

Here $\beta_x^{(r)}$ is the sequence equal to $\beta_x(n)$ when $\gcd(n, r) = 1$ and to $0$
otherwise, $\Delta(\cdot\,; a \bmod q)$ is the discrepancy in the residue class of $a$ modulo $q$,
and $\tau(m)$ is the number of positive divisors of $m$.

## Sources

- Polymath8b v4, Claim 2.6 and its uniformity footnote.
