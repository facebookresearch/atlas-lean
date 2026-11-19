# Generating function for restricted smooth words ending in their largest letter

For
$i \ge 1$, let $s^*(n, i; q)$ be the capacity distribution of the restricted smooth words of
length $n$ that end in $i$ and all of whose letters are at most $i$. For $j \ge 1$, let
$t^*(m, j; q) = \sum_w q^{w_1 + \cdots + w_m}$, the sum over the words $w = w_1 \cdots w_m$ over
$\{1, \dots, j\}$ with $w_1 = w_m = j$ (there are none for $m = 0$), consecutive letters
differing by at most $1$ and no two adjacent letters equal to $1$, and let
$T^*_j(q^{j+1} x; 1/q) = \sum_{m \ge 0} q^{(j+1)m}\, t^*(m, j; 1/q)\, x^m$. Then, in the ring of
formal power series in $x$ over $\mathbb{Z}[q, q^{-1}]$,

$$
\sum_{n \ge 0} s^*(n, i; q)\, x^n =
x^i \prod_{j=1}^{i-1} \frac{1}{1 - x - x\, T^*_j(q^{j+1} x; 1/q)},
$$

where each denominator has constant term $1$ and so is invertible.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 11.
