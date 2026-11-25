# Perfect covers of $(\mathbb{Z}_2)^m \oplus \mathbb{Z}_{2^n}$

Write $C(K)$ for the number
of perfect covers of a group $K$, and for natural numbers $m$ and $n$ let
$b_{m,n} = C((\mathbb{Z}_2)^m \oplus \mathbb{Z}_{2^n})$. Then:
for every $m \ge 0$, $C((\mathbb{Z}_2)^m) \cdot m! = \prod_{i=0}^{m-1} (2^m - 2^i)$;
for all $m, n \ge 1$, writing $B_{m,k} = 2^m \prod_{i=0}^{k-1} (2^m - 2^i) / (k+1)!$ for
$1 \le k \le m$, we have $b_{m,n} = 2^{m+n-1} b_{m,n-1} +
\sum_{k=1}^{m} B_{m,k} \, 2^{k(m-k)} \, 2^{(k+1)(n-1)} \, b_{m-k,n-1}$;
and for every $m \ge 0$ there is a polynomial $q$ of degree $m$ with rational coefficients such
that $b_{m,n} = 2^{m(n-1)} \, 2^{n(n-1)/2} \, q(n)$ for all $n \ge 0$, where the power
$2^{m(n-1)}$ has an integer exponent (it is $2^{-m}$ at $n = 0$).

## Sources

- John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 4 (`jis-2025-25.7.8-thm-4`).
