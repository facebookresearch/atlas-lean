# Stable Steinberg Finite Weyl Kernel Factorization

Finite central-kernel elements factor as cocycle times finite torus.

Purpose: compose the paired-word bridge with the weighted normal form so that
`g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n` over `[Field F]`
yields `c` in the torus cocycle subgroup and `t` in the rank-`n` finite torus
subgroup with `g = c * t`. Orientation is head-left throughout, matching
`weightedWeylProd`; the factors are existential. The empty word gives
`1 = 1 * 1`, uniform in ranks `n = 0, 1`.

Nonclaims: factorization only; no finite-torus-kernel landing, cocycle
containment, finite-stage reduction, TWT, inverse, naturality, or Matsumoto
claim.
