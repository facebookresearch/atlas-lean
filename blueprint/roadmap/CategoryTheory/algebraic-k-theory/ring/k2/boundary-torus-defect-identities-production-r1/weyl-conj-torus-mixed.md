# Weyl conj torus mixed

Mixed Weyl conjugation of a torus generator, modulo the torus cocycle.

Hypotheses: `[Field F]`, pairwise-distinct indices `i ≠ j` (`hij`),
`i ≠ k` (`hik`), `k ≠ j` (`hkj`), units `u v : Fˣ`.

Exact orientation: `weyl i k u * torus k j v * (weyl i k u)⁻¹ =
c * torus i j v` with the cocycle defect `c ∈ torusCocycleSubgroup`
exhibited on the left. The torus parameter is unchanged (`v`): the mixed
Weyl rewrite `weyl_conj_weyl_mixed` sends the conjugated torus word to
the same-pair product `weyl i j (u * v) * weyl i j (-u)`, and
`weyl_samePair_mul_eq_cocycle_mul_torus` rewrites that product to a left
defect times `torus i j v`, since `(-(u * v)) * (-u)⁻¹ = v` in `Fˣ`.

Purpose: transports a torus generator on the mixed three-index
configuration `(k, j)` across the Weyl generator on `(i, k)`; the
subsequent three-index transfer packet consumes exactly this orientation.

Edge cases: `u` and `v` are arbitrary units (including `1` and `-1`);
the unit/sign/inverse computation uses `mul_neg`, `mul_comm`,
`mul_inv_cancel₀` with `neg_ne_zero`, and `Units.ext` coercion algebra,
hence is valid in characteristic two where `-1 = 1`.

Nonclaims: no defect-free equality (`c = 1` is false in general), no
ordered torus normal form, no finite-central containment, no TWT
closure, no kernel generation, and no Matsumoto comparison or
isomorphism.
