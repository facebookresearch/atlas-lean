# Power-weighted convolution of Fibonacci $m$-step numbers

Let $m \ge 1$ and let
$F \colon \mathbb{N} \to \mathbb{N}$ satisfy $F(0) = 0$, $F(1) = 1$ and
$F(k) = \sum_{j=1}^{m} F(k - j)$ for every $k \ge 2$, where a term $F(k - j)$ with $j > k$ is
read as $F(0) = 0$. Then for every natural number $n$,

$$\sum_{j=0}^{n} 2^j F(n - j) = 2^{n+m-1} - F(n + 1 + m),$$

where the subtraction on the right is taken in $\mathbb{N}$ (truncated at $0$).

The initial conditions are those of the paper's definition of Fibonacci $m$-step numbers
(lines 126–133), whose values at negative indices are $0$. The paper states the theorem for
$m \ge 3$; the cases $m = 1$ and $m = 2$ also hold, so the hypothesis here is $m \ge 1$.

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci m-Step Numbers," Journal of Integer Sequences 27 (2024), Article 24.8.8, Theorem (label power2_conv), lines 453–459, https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.tex
