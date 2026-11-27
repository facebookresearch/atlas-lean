# Series asymptotics for the shifted floor residue count with $r = 1$

Let $m \ge 2$ be a
natural number and let $\alpha$ and $\nu$ be real numbers with $0 \le \alpha < 1$ and
$0 \le \nu < 1$. For a natural number $n$ let $\mathcal N_{n,\alpha,\nu,1,m}$ be the number of
integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv 1 \pmod m$, and put

$$S = \sum_{i \ge 0} \Bigl( \frac{1}{1 + im - \alpha} - \frac{1}{2 + im - \alpha} \Bigr).$$

Then there is a constant $C$ such that

$$\Bigl| \mathcal N_{n,\alpha,\nu,1,m} - \Bigl( -\frac{\alpha n}{1 - \alpha} + nS \Bigr) \Bigr| \le
C \sqrt n$$

for every natural number $n \ge 1$ with $\nu \le n\alpha$.

## Sources

- Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024), Article 24.2.5, Corollary 35 (`jis-2024-24.2.5-cor-35`).
