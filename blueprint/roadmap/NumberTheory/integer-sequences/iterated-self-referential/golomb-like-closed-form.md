# Closed form for Golomb-like sequences

Let $y$ and $z$ be integers of opposite parity with
$y \ge 2$ and $z \ge 2 - y$, and put $c = (y + z - 1)/2$. There is exactly one strictly
increasing function $f$ from the positive integers to the positive integers such that
$f(1) = (y + z + 1)/2$ and $f(f(n)) = yn + z$ for every positive integer $n$. Moreover, for
every such $f$, every natural number $k$ and every integer $j$ with $-c\,y^k \le j < c\,y^k$,
the rational number

$$m = \frac{(y+1)\,c}{y-1}\, y^k - \frac{z}{y-1} + j$$

is a positive integer and

$$f(m) = \frac{2c}{y-1}\, y^{k+1} - \frac{z}{y-1} + \frac{(y+1)\,j}{2} + \frac{(y-1)\,|j|}{2}.$$

Proof: The construction tiles the positive integers by the source's blocks and verifies the
two slope regimes, followed by strong-induction uniqueness, as in Cloitre–Sloane–Vandermast,
Theorem Th1 and equations (Eq48a), (Eq48).

## Sources

- Benoit Cloitre, N. J. A. Sloane, and Matthew J. Vandermast, "Numerical Analogues of Aronson's Sequence," Journal of Integer Sequences 6 (2003), Article 03.2.2, Theorem, equations, lines 584–603, https://cs.uwaterloo.ca/journals/JIS/VOL6/Cloitre/cloitre2.tex
