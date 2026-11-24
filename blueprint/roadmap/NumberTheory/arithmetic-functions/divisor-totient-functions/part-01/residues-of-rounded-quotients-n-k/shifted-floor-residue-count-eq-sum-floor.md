# Floor-sum formulas for the shifted floor residue counts

Let $n$ and $m$ be natural
numbers with $m \ge 2$, and let $\alpha$ and $\nu$ be real numbers with $0 \le \alpha < 1$,
$0 \le \nu < 1$ and $\nu \le n\alpha$. For an integer $r$ let $\mathcal N_{n,\alpha,\nu,r,m}$ be
the number of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$. Then

$$\mathcal N_{n,\alpha,\nu,1,m} = n - \Bigl\lfloor \frac{n - \nu}{1 - \alpha} \Bigr\rfloor +
\sum_{i=0}^{n} \Bigl( \Bigl\lfloor \frac{n - \nu}{1 + im - \alpha} \Bigr\rfloor -
\Bigl\lfloor \frac{n - \nu}{2 + im - \alpha} \Bigr\rfloor \Bigr),$$

and for every natural number $r$ with $2 \le r \le m$,

$$\mathcal N_{n,\alpha,\nu,r,m} = \sum_{i=0}^{n} \Bigl( \Bigl\lfloor \frac{n - \nu}{r + im - \alpha}
\Bigr\rfloor - \Bigl\lfloor \frac{n - \nu}{r + 1 + im - \alpha} \Bigr\rfloor \Bigr).$$

The paper sums over all $i \ge 0$; the terms with $i > n$ vanish, because for them every
denominator exceeds $n - \nu \ge 0$.

## Sources

- Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024), Article 24.2.5, Proposition 25 (`jis-2024-24.2.5-prop-25`).
