# Perron-vector inequality for essentially non-negative matrices

Let $A$ be an irreducible $n \times n$ real matrix with non-negative off-diagonal entries (an ML-matrix) and $D$ a real diagonal matrix. Let $r(\cdot)$ denote the spectral abscissa (for irreducible ML-matrices, the Perron root), and for an irreducible ML-matrix $B$ let $v(B) > 0$ be its right Perron vector with $\mathbf 1^\top v(B) = 1$ and $u(B) > 0$ its left Perron vector with $u(B)^\top v(B) = 1$.

**Theorem.**

$$r(A + D) - r(A) \le u(A + D)^\top D\, v(A + D),$$

with equality if and only if $D = cI$ for some $c \in \mathbb R$.

**Corollary.** Equivalently,

$$u(A + D)^\top A\, v(A + D) \le r(A),$$

with equality if and only if $D = cI$. More generally, if $A = \sum_{k=1}^N M_k$ with ML-matrices $M_k$ sharing a common right (or left) Perron vector, then $u(A + D)^\top A\, v(A + D) \le \sum_k r(M_k)$.

**Corollary (convexity form).** For $\beta > 1$,

$$r(A + D) - r(A) \le r\big(\tfrac1\beta A + D\big) - r\big(\tfrac1\beta A\big) \le u(A + \beta D)^\top D\, v(A + \beta D),$$

with equality if and only if $D = cI$.

**Corollary ("flip").** If $y, z > 0$ satisfy $y \circ z = u(A) \circ v(A)$ (entrywise product), then $z^\top A\, y \ge u(A)^\top A\, v(A) = r(A)$, with equality iff $y = v(A)$; in particular $v(A)^\top A\, u(A) > r(A)$ whenever $u(A) \neq v(A)$.

In words: weighting the mixing matrix $A$ by the Perron vectors of a perturbed system $A + D$ never yields more than the Perron root of $A$ itself.

## Expansion

The Donsker–Varadhan–Friedland variational formula expresses the Perron root of an irreducible ML-matrix as a min–max over probability vectors, $r(A) = \sup_{x}\inf_{p} \sum_i p_i (Ax)_i/x_i$, with unique critical points determined by the Perron vectors. Evaluating the formula for $A$ at the critical points of $A + D$ gives an upper bound for $r(A)$ from below in the right direction: the diagonal part contributes exactly $\sum_i u_i v_i d_i = u^\top D v$, which yields $r(A + D) - r(A) \le u^\top D v$. Uniqueness of the critical points gives the equality case. Since $u^\top (A + D) v = r(A + D)$, subtracting yields the corollary $u^\top A v \le r(A)$.

## Sources

- Lee Altenberg, "Karlin Theory On Growth and Mixing Extended to Linear Differential Equations", arXiv (2010). Notation section (spectral abscissa, Perron vector normalization, variational formula), Theorem 1, Corollaries 2–5. <https://doi.org/10.48550/arXiv.1006.3147>
