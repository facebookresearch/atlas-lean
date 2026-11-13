# Digit decomposition of the Irwin measures, positive index

Let $b > 1$ and $d < b$ be
natural numbers, and for each natural number $j$ let $\mu_j$ be the Irwin measure of base $b$ and
digit $d$ with index $j$. Let $f : \mathbb{R} \to \mathbb{R}$ be measurable and bounded on
$[0, b)$, and let $k \ge 1$. Then

$$\int_{[0,1)} f(bx)\, d\mu_k(x) =
\frac{1}{b} \sum_{a \ne d} \int_{[0,1)} f(a + x)\, d\mu_k(x) +
\frac{1}{b} \int_{[0,1)} f(d + x)\, d\mu_{k-1}(x),$$

where $a$ ranges over the digits $0, 1, \dots, b - 1$ other than $d$.

Measurability of $f$ is a hypothesis added to the paper's boundedness assumption.

## Sources

- Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Lemma 1.
