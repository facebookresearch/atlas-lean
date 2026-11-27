# Series asymptotics for the shifted floor residue counts with $2 \le r \le m$

Let $r$ and
$m$ be natural numbers with $2 \le r \le m$, and let $\alpha$ and $\nu$ be real numbers with
$0 \le \alpha < 1$ and $0 \le \nu < 1$. For a natural number $n$ let
$\mathcal N_{n,\alpha,\nu,r,m}$ be the number of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$, and put

$$S = \sum_{i \ge 0} \Bigl( \frac{1}{r + im - \alpha} - \frac{1}{r + 1 + im - \alpha} \Bigr).$$

Then there is a constant $C$ such that
$\bigl| \mathcal N_{n,\alpha,\nu,r,m} - nS \bigr| \le C \sqrt n$ for every natural number
$n \ge 1$ with $\nu \le n\alpha$.

## Sources

- Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024), Article 24.2.5, Corollary 34 (`jis-2024-24.2.5-cor-34`).
