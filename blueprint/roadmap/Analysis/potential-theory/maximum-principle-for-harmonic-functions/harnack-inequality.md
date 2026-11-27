# Harnack's inequality for harmonic functions

Let $U$ be an open subset of a finite-dimensional real inner product space and let $V$ be open and
connected with $\overline V$ compact and contained in $U$. There is a constant $C > 0$, depending
only on $V$ and $U$, such that every nonnegative harmonic function $u$ on $U$ satisfies

$$u(x) \le C \, u(y) \qquad \text{for all } x, y \in V,$$

equivalently $\sup_V u \le C \inf_V u$. The constant is chosen before $u$.

Harnack's inequality bounds a nonnegative harmonic function on a compact
part of the domain independently of its boundary values; Evans's entropy notes derive it for
divergence-form equations from an interior bound on $|D \log u|$, and deduce the strong maximum
principle from it.

## Informally uses

- [Mean-value property of harmonic functions, and its converse](harmonic-on-nhd-iff-forall-average-close.md):
  Schmidt's proof compares ball averages of $u$ on nested balls.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 3 (Laplace equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf), Harnack's Inequality 3.8.
- L. C. Evans, *Entropy and Partial Differential Equations*, lecture notes, [entropy.and.PDE.pdf](https://math.berkeley.edu/~evans/entropy.and.PDE.pdf), Chapter IV.A.3, Theorem 3.
