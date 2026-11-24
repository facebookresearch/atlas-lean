# Fourth-power sum of coordinate differences over a box

Let $p$ be a prime and $N$ a
natural number, and let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$
with $|a_i| \le N$ for all $i$. Then

$$\sum_{i=1}^{p-1} \sum_{j=1}^{p-1} \sum_{a, b \in B(p, N)} (a_i - b_i)^2 (a_j - b_j)^2 =
(2N+1)^{2(p-1)} \cdot \tfrac{2}{45} N (N+1) (p-1) (10N^2 p + 4N^2 + 10Np + 4N - 3).$$

This corrects the paper's printed right side, which omits the factor $(2N+1)^{2(p-1)}$: for
$p = 3$ and $N = 1$ the sum is $936$, while the printed right side is $104/9$. The paper's own
proof carries the factors $(2N+1)^{2p-4}$ and $(2N+1)^{2p-6}$ in its pieces (10) and (11), and
combining them gives the value above; the printed formula is the sum divided by
$|B(p, N)|^2 = (2N+1)^{2(p-1)}$. The paper takes $p$ an odd prime; here only $p$ prime is
assumed.

## Sources

- Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10, Lemma 5.
