# Orthonormal error contrast diagonalizing the relationship matrix

Let $m$, $k$ and $r$ be finite index sets, $X$ a real $m \times k$ matrix (the fixed-effect
design), $K$ a real $m \times m$ matrix (the relationship matrix), $B$ a real $r \times m$ matrix
and $d \in \mathbb{R}^r$. Then $B$ is an orthonormal error contrast for $X$ that diagonalizes $K$
with eigenvalues $d$ when the following four conditions hold:

- $BX = 0$: $B$ annihilates the fixed effects;
- $BB^\top = I$: the rows of $B$ are orthonormal;
- $|r| + |k| = |m|$;
- $BKB^\top = \operatorname{diag}(d)$.

The $d_i$ are then the eigenvalues of $BKB^\top$. The definition does not require $K$ to be
symmetric.
