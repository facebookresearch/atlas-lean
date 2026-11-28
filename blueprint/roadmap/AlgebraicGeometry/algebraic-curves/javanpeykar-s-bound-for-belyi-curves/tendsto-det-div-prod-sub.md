# The confluent determinant limit

**The confluent determinant limit** (R. de Jong, *Arakelov invariants of Riemann surfaces*,
Doc. Math. 10 (2005), proof of Lemma 3.2, p. 317, second equality of the limit display; the
determinant `W_z` is defined on p. 314).

Let `U ⊆ ℂ` be open, `a ∈ U`, and `f_0, …, f_{g-1}` holomorphic on `U`. Then, as
`z = (z_0, …, z_{g-1})` tends to `(a, …, a)` through tuples of pairwise distinct points of `U`,
`det (f_k(z_l))_{k,l} / ∏_{k<l} (z_l - z_k) → det (f_k^{(l)}(a) / l!)_{k,l}`,
where `f^{(l)} = iteratedDeriv l f` and `k, l` run over `Fin g`, so the column index `l` here is
de Jong's `l - 1`. The hypothesis `g ≥ 1` of the source is not needed (for `g = 0` both sides are
`1`). De Jong states the limit for absolute values, `|det| / ∏_{k<l} |z_k - z_l| → |W_z|`; the
signed limit proved here implies it.
