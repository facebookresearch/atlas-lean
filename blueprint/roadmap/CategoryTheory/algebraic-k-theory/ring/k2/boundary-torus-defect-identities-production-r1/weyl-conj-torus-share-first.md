# Weyl conj torus share First

Share-first Weyl conjugation of a torus generator, modulo the torus cocycle.

Hypotheses: `[Field F]`, pairwise-distinct indices `i ≠ j` (`hij`),
`i ≠ k` (`hik`), `k ≠ j` (`hkj`), arbitrary units `u v : Fˣ`
(including `1` and `-1`).

Exact share-first orientation: `weyl i k u * torus i j v * (weyl i k u)⁻¹ =
c * torus k j v` with the cocycle defect `c ∈ torusCocycleSubgroup`
exhibited on the left. The torus parameter is unchanged (`v`): the
conjugating Weyl rewrites via `weyl_swap` to `weyl k i (-u⁻¹)`, and the
existing `weyl_conj_torus_mixed` at `(k, j, i)` closes the goal with no
new unit algebra.

Purpose: rank-free transport of a share-first torus generator across its
shared-index Weyl generator; the overlap-word packet consumes exactly this
orientation with no rank bound.

Nonclaims: no defect-free equality (`c = 1` is false in general), no
finite(-central) containment, no TWT closure, no ordered torus normal form,
no kernel generation, and no Matsumoto comparison or isomorphism.
