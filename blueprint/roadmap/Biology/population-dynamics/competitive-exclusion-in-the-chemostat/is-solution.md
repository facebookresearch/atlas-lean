# Forward solutions of the multispecies chemostat

`(S, x)` solves the chemostat at every
time `t ≥ 0`: `S'(t) = (S⁰ - S(t)) D - ∑ᵢ (1/yᵢ) mᵢ xᵢ(t) S(t) / (aᵢ + S(t))` and, for every
species `i`, `xᵢ'(t) = xᵢ(t) (mᵢ S(t) / (aᵢ + S(t)) - D)`. The derivatives are two-sided
(`HasDerivAt`) at `t = 0` too, so a trajectory given only on `[0, ∞)` must be extended to negative
times with these derivatives at `0`; one that is only right-differentiable at `0` does not
qualify. A solution on an open interval containing `[0, ∞)` qualifies, and negative times matter
only through the derivatives at `0`.
