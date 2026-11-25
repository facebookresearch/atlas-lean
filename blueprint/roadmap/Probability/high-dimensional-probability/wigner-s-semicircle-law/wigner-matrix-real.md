# Normalised real Wigner matrix

For an array $Z : \mathbb{N} \times \mathbb{N} \to (\Omega \to \mathbb{R})$ and $N \ge 1$, the real
symmetric matrix

$$X_N(i, j) = \frac{Z_{\min(i,j), \max(i,j)}}{\sqrt{N}}, \qquad 0 \le i, j < N,$$

built from the upper-triangular part of $Z$. With independent centred entries of variance $1$ off the
diagonal, this is the normalisation of Anderson, Guionnet and Zeitouni under which the spectrum
fills $[-2, 2]$; their diagonal entries $Y_i/\sqrt{N}$ are the $Z_{ii}/\sqrt{N}$ here.

This is the [Wigner matrix](wigner-matrix.md) divided by $\sqrt{N}$ and kept real.

## Background

- [Wigner matrix](wigner-matrix.md): the unnormalised complex form used in the statement of the
  semicircle law.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), (2.1.2).
