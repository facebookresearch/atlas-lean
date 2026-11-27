# Dantzig's rule makes 2^n - 1 pivots on the Klee-Minty program

For every $n$ and every linearly ordered field, the simplex method with Dantzig's rule, started from the slack dictionary of the $n$-dimensional Klee-Minty program, performs exactly $2^n - 1$ pivots before reaching an optimal dictionary, visiting every vertex of the deformed cube. Hence the simplex method with Dantzig's rule has exponential worst-case running time.

## Proof sketch

Induction on $n$: the run on dimension $n + 1$ consists of the run on dimension $n$, one pivot entering $x_{n+1}$, and the run on dimension $n$ reversed, giving $2(2^n - 1) + 1$ pivots; the dictionaries along the way are computed explicitly.

## Depends on

- [The Klee-Minty program](klee-minty-program.md)

## Proof depends on

- [Soundness of the simplex method with Dantzig's rule](dantzig-rule-soundness.md)

## Sources

- V. Klee and G. J. Minty, "How Good is the Simplex Algorithm?", in O. Shisha (ed.), Inequalities III, Academic Press, 1972.
- V. Chvátal, "Linear Programming", W. H. Freeman, 1983.
