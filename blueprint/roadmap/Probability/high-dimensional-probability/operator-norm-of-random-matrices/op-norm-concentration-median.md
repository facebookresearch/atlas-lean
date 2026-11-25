# Concentration of the operator norm

There are absolute constants $C, c > 0$ with the following property. Let $M$ be a random
$n \times n$ real matrix whose entries are independent, have mean zero and are bounded by $1$ in
absolute value, and let $m$ be a median of $\|M\|$, the operator norm on Euclidean space. Then

$$\mathbb{P}\big(\big|\|M\| - m\big| \ge \lambda\big) \le C e^{-c\lambda^2} \quad \text{for every }
\lambda > 0.$$

The constants do not depend on $n$, so $\|M\|$, which is $O(\sqrt{n})$, fluctuates by $O(1)$.

Tao's statement allows complex entries; this is the real case.

## Informally uses

- [Talagrand's concentration inequality around a median](../../concentration-inequalities/talagrand-s-concentration-inequality/talagrand-concentration-median.md):
  the proof applies it to $F(M) = \|M\|$, which is convex, and $1$-Lipschitz for the Frobenius
  norm because the operator norm is at most the Frobenius norm.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, Proposition 2.3.10.
