# The Mandelbrot set is connected (Douady–Hubbard)

The Mandelbrot set, the set of all
$c \in \mathbb{C}$ for which the sequence $(T_c^n(0))_{n \ge 0}$ of iterates of $0$ under
$T_c(z) = z^2 + c$ is bounded, is a nonempty connected subset of $\mathbb{C}$.

## Sources

- Adrien Douady and John H. Hubbard, *Étude dynamique des polynômes complexes I, II*, Publ. Math. Orsay 84-02,
  85-04 (1984–1985).
- Oliver Knill, *Some Fundamental Theorems in Mathematics* (2023), §62 (Quadratic map; the theorem of the
  section), <https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf>.
- Problem `mandelbrot_connected` of the lean-eval benchmark.
