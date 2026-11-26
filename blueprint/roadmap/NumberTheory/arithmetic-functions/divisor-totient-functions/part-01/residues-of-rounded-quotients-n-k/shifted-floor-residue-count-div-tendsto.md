# Limiting densities of the shifted floor residue counts

Let $r$ and $m$ be natural
numbers with $1 \le r \le m$, and let $\alpha$ and $\nu$ be real numbers with $0 \le \alpha < 1$
and $0 \le \nu < 1$. For a natural number $n$ let $\mathcal N_{n,\alpha,\nu,r,m}$ be the number
of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$, and for a natural number $s$ put

$$I_s = \int_0^1 \frac{(1 - x)\, x^{s - 1 - \alpha}}{1 - x^m} \, dx.$$

Then, as $n \to \infty$, $\mathcal N_{n,\alpha,\nu,r,m}/n$ tends to $-\alpha/(1 - \alpha) + I_1$
if $r = 1$ and to $I_r$ if $r \ge 2$.

## Sources

- Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024), Article 24.2.5, Corollary 38 (`jis-2024-24.2.5-cor-38`).
