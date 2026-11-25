# Basis generating polynomials of matroids are Lorentzian

If $M$ is a matroid of rank $d$ whose ground set is contained in $[n]$, then its basis generating polynomial

$$f_M(w) = \sum_{B \text{ base of } M} \prod_{i \in B} w_i$$

lies in $L^d_n$.

This is the implication (8) ⇒ (4) of Brändén and Huh's Theorem 3.10 (for a set $J$ of zero-one
vectors the generating function $\sum_{\alpha \in J} w^\alpha / \alpha!$ of the paper is this
polynomial, since $\alpha! = 1$). As Brändén and Huh record after Theorem 3.10, the
log-concavity of $f_M$ on the positive orthant was also shown by Anari, Oveis Gharan and
Vinzant. The statement contrasts with stable polynomials:
no stable polynomial has the bases of the Fano plane as its support.

## Informally uses

- [Base vectors of a matroid are M-convex](is-mconvex-base-vectors.md): the support of $f_M$ is
  the set of base vectors, which is M-convex.
- [Lorentzian polynomials as the closure of strictly Lorentzian polynomials](theorem-2-25.md):
  the proof checks the quadratic derivatives $\partial^\alpha f_M$ (Lemma 3.11) and concludes
  with Theorem 2.25.

## Sources

- P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Theorem 3.10, Lemma 3.11 and Remark 3.6, https://arxiv.org/abs/1902.03719.
