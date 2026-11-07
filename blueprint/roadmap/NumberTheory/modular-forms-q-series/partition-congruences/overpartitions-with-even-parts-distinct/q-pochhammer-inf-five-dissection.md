# Ramanujan's 5-dissection of Euler's product

Let $q$ be a complex number with
$|q| < 1$. For $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{n \ge 0} (1 - q^k q^{kn})$, and
for complex $a$, $b$ with $|a|, |b| < 1$ let $f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2}
b^{n(n-1)/2}$ be Ramanujan's general theta function; all these products and series converge,
so the raw infinite product and the raw theta sum take these values. For $|x| < 1$ put
$R(x) = f(-x, -x^4) / f(-x^2, -x^3)$. Then
$f_1 = f_{25} \left( R(q^5)^{-1} - q - q^2 R(q^5) \right)$.

## Sources

- Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 5 (`integers-2025-A69-lem-5`).
