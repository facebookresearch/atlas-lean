# Weak diffusion ibp

Integration by parts for the primitive of an `L²` function against a
`WeakH10` test function: `∫ F * v' = -∫ f * v`, where `F x = ∫ s in 0..x,
f s`. Both `F` and `v.toFun` are absolutely continuous on `[0,1]`, with
derivatives `f` and `v.weakDeriv` almost everywhere, so Mathlib's
integration by parts for absolutely continuous functions applies; the
boundary terms vanish because `v 0 = v 1 = 0`.
