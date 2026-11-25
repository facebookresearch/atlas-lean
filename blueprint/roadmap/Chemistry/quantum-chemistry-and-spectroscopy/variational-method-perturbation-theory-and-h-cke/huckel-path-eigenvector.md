# Hückel eigenvectors of a path graph

Hückel path eigenvector: on the path with `n` vertices, for `1 ≤ k ≤ n`, the Hückel matrix maps the
sine mode `j ↦ sin (k * (j + 1) * π / (n + 1))` (`j = 0, …, n - 1`) with wavenumber `k` to
`α + 2 * β * cos (k * π / (n + 1))` times itself. The mode is nonzero (its first entry is
`sin (k * π / (n + 1)) > 0`, see [nonzero path sine modes](huckel-path-sine-mode-ne-zero.md)), so it
is an eigenvector with this eigenvalue.
