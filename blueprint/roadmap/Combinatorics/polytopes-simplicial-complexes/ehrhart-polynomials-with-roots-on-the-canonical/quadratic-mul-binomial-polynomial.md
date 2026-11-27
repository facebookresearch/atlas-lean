# Multiplying a binomial polynomial by a quadratic

For an integer $n$ and a natural number
$k$, write $\binom{X+n}{k} = \frac{1}{k!} \prod_{i=0}^{k-1} (X + n - i)$ for the real binomial
polynomial. Let $d$ and $j$ be natural numbers with $0 < d$ and $j \le d$, and let $c$ be a real
number. Then

$$
(X^2 + X + c) \binom{X+d-j}{d} = \alpha \binom{X+d-j+2}{d+2} + \beta \binom{X+d-j+1}{d+2} +
\gamma \binom{X+d-j}{d+2},
$$

where $\alpha = j^2 + j + c$, $\beta = 2(dj - j^2 + d + 1 - c)$ and
$\gamma = d^2 - 2dj - j + j^2 + d + c$.

The paper assumes $c \ge 1/4$; the identity holds for every real $c$.

## Sources

- Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*, INTEGERS 25 (2025), Article A68, Lemma 7.
