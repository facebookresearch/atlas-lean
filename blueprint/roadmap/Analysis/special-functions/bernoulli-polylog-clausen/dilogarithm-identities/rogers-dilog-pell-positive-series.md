# Bridgeman's dilogarithm series for a positive Pell solution

Write
$L(x) = \sum_{m \ge 1} x^m/m^2 + \frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on
$[0, 1]$ (with $\log 0 = 0$). Let $n$ be a natural number that is not a perfect square, let
$a, b$ be positive rationals with $a^2 - n b^2 = 1$, and put $u = a + b\sqrt{n}$. Define rationals
$a_k, b_k$ by $a_0 = 1$, $b_0 = 0$, $a_{k+1} = a a_k + n b b_k$ and $b_{k+1} = b a_k + a b_k$,
so that $u^k = a_k + b_k\sqrt{n}$. Then

$$
L(1/u^2) = \sum_{k \ge 2} L(b^2/b_k^2),
$$

and if $a$ and $b$ are integers, then for every $k \ge 0$ there is an integer $m$ with $b_k = bm$.

## Sources

- Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*, INTEGERS 25 (2025), Article A52, Theorem 3 (3), quoting Bridgeman (`integers-2025-A52-thm-3`).
