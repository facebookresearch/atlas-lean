# Generating series of a Gibonacci sequence

Let $a$ and $b$ be integers and let
$(G_n)_{n \ge 0}$ be the Gibonacci sequence with $G_0 = a$ and $G_1 = b$. In the ring
$\mathbb{Q}[[X]]$ of formal power series with rational coefficients,

$$(1 - X - X^2) \sum_{n \ge 0} G_n X^n = a + (b - a) X.$$

This is the product form of the quotient $\frac{(b - a)x + a}{1 - x - x^2}$ for the generating
function of $(G_n)$.

## Sources

- Knapp, *Fibonacci Generating Functions*, Journal of Integer Sequences 27 (2024), Article 24.3.1, Lemma 5 (`jis-2024-24.3.1-lem-5`).
