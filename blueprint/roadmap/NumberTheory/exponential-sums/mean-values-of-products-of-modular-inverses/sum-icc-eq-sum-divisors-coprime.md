# Splitting a sum by greatest common divisor

For every function
$f : \mathbb{N} \to \mathbb{C}$ and every natural number $n$,

$$\sum_{k=1}^{n} f(k) = \sum_{d \mid n} \sum_{1 \le h \le n/d,\ \gcd(n/d, h) = 1} f(hd).$$

Here $d$ runs over the positive divisors of $n$, and $0$ is taken to have none, so for $n = 0$
both sides are empty sums.

## Sources

- O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular Inverse*, INTEGERS 24 (2024), Article A33, Lemma 5.
