# Hambly–Lyons uniqueness theorem: trivial signature iff tree-like

Let $T \ge 0$ and let $X : [0, T] \to \mathbb{R}^d$ (Euclidean norm) be the absolutely
continuous path $X_t = \int_0^t v(u)\,du$ with velocity $v$ integrable on $[0, T]$. Then $X$ is
[tree-like](is-tree-like.md) if and only if its signature over $[0, T]$ is trivial:

$$S(X)_{0,T} = (1, 0, 0, \dots).$$

Hambly and Lyons prove this for every path of bounded variation (their Theorem 1); the
statement above is its case of absolutely continuous paths.

Combined with Chen's identity and [time reversal](../signature-of-a-path/tensor-mul-signature-reverse.md),
the theorem says that two paths of bounded variation have the same signature exactly when one
followed by the other run backwards is a Lipschitz tree-like path (their Corollary 1.5); the
classes form a group, and each class contains a unique path of minimal length, the reduced path
(Corollaries 1.6 and 1.7). The theorem extends Chen's uniqueness theorem for irreducible piecewise
regular paths. Boedihardjo, Geng, Lyons and Yang extend it to weakly geometric rough paths in
Banach spaces (Adv. Math. 293 (2016), arXiv:1406.7871, Theorem 1.1).

## Background

- [Signature of a path](../signature-of-a-path/signature.md): the iterated integrals whose
  vanishing characterises tree-like paths.
- [Universal approximation by linear functionals of the signature](../signature-of-a-path/exists-signature-linear-approx.md):
  why a time coordinate is added in applications, to rule out tree-like ambiguity.

## Sources

- B. Hambly and T. Lyons, *Uniqueness for the signature of a path of bounded variation and the
  reduced path group*, Ann. of Math. 171 (2010), arXiv:math/0507536, Theorem 1 and
  Corollaries 1.5–1.7.
