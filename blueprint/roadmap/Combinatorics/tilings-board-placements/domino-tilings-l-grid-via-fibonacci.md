# Tauraso's Cassini-type identity

Let $f_n$ be the Fibonacci numbers, with $f_0 = 0$ and
$f_1 = 1$. For natural numbers $n, m$ put $L_{n,m} = f_{n+1} f_m + f_n f_{m+1}$ and
$a_n = f_{n+1} f_{n-1} + f_n^2$, where $n - 1$ is truncated subtraction. Then
$L_{n,m} = f_{n+1} f_m + f_n f_{m+1}$ for all $n, m \ge 1$, $L_{n,n-1} = a_n$ for all
$n \ge 2$, and $L_{n,n-1}^2 = L_{n,n} L_{n-1,n-1} + 1$ for all $n \ge 2$.

In the source $L_{n,m}$ is the number of domino tilings of the L-grid, and the Fibonacci
formula for it is a theorem. Here $L_{n,m}$ is defined by that formula, so the first two
equations hold by definition and the content is the Cassini-type identity.

## Sources

- Roberto Tauraso, "A New Domino Tiling Sequence," Journal of Integer Sequences 7 (2004), Article 04.2.3, Lemma (Section 2, equations Lformula and Lcassini), lines 200–221, https://cs.uwaterloo.ca/journals/JIS/VOL7/Tauraso/tauraso3.tex
