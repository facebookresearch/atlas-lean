# Torus zero last mem normalizer finite Stage

Common-base torus normalizes the lower finite stage.

For `0 < n` and `u : Fˣ`, `torus 0 n u` normalizes `finiteStage n`.
For a generator `x p q a` with `p,q < n`, split on `p = 0` and `q = 0`:
use `torus_conj_x_ik` for `x 0 q`, `torus_conj_x_ki` for `x p 0`,
and `torus`/`weyl` unfolding plus `x_comm` when both are disjoint from
`0,n`. Both directions of `mem_normalizer_iff` hold; the inverse direction
uses inverse coefficient rescaling. Every resulting root keeps both indices
`< n`.
