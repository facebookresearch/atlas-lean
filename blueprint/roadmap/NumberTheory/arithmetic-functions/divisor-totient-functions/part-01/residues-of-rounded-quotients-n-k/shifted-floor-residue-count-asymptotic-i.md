# Integral asymptotics for the shifted floor residue counts

Let $m \ge 1$ be a natural
number and let $\alpha$ and $\nu$ be real numbers with $0 \le \alpha < 1$ and $0 \le \nu < 1$.
For natural numbers $n$ and $r$ let $\mathcal N_{n,\alpha,\nu,r,m}$ be the number of integers $k$
with $1 \le k \le n$ such that $\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$, and put

$$I_r = \int_0^1 \frac{(1 - x)\, x^{r - 1 - \alpha}}{1 - x^m} \, dx.$$

Then there is a constant $C$ such that

$$\Bigl| \mathcal N_{n,\alpha,\nu,1,m} - \Bigl( -\frac{\alpha n}{1 - \alpha} + n I_1 \Bigr) \Bigr|
\le C \sqrt n$$

for every natural number $n \ge 1$ with $\nu \le n\alpha$, and for every natural number $r$ with
$2 \le r \le m$ there is a constant $C_r$ such that
$\bigl| \mathcal N_{n,\alpha,\nu,r,m} - n I_r \bigr| \le C_r \sqrt n$ for every natural number
$n \ge 1$ with $\nu \le n\alpha$.

## Sources

- Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024), Article 24.2.5, Theorem 37 (`jis-2024-24.2.5-thm-37`).
