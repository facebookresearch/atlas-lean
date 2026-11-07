# Large sets of grid cells with no $r \times r$ all-ones submatrix

For all natural numbers
$r \ge 2$ and $n \ge 1$ there is a set $S$ of cells of the $n \times n$ grid
$\{0, \dots, n - 1\}^2$ with $|S| \ge \frac{1}{2} n^{2 - 2/(r+1)}$ that contains no $r \times r$
all-ones submatrix: there are no sets $R, C \subseteq \{0, \dots, n - 1\}$ with $|R| = |C| = r$
and $R \times C \subseteq S$.

In the language of 0-1 matrix extremal functions this says $\operatorname{ex}(n, J_{r,r}) \ge
\frac{1}{2} n^{2-2/(r+1)}$ for the $r \times r$ all-ones matrix $J_{r,r}$; it is the cited
Kővári–Sós–Turán-type lower bound, with the paper's explicit constant.

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 4.4 (`integers-2024-A1-lem-4-4`).
