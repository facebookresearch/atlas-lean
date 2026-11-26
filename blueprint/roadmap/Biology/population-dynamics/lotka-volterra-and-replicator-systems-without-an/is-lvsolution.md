# Forward solutions of the Lotka–Volterra system

`y` solves `yᵢ' = yᵢ (rᵢ + ∑ⱼ Cᵢⱼ yⱼ)`,
with the library's field `lvField r C`, at every time `t ≥ 0`. The derivative is two-sided
(`HasDerivAt`) at `t = 0` too, so a trajectory given only on `[0, ∞)` must be extended to
negative times with that derivative at `0`; one that is only right-differentiable at `0` does
not qualify. A solution on an open interval containing `[0, ∞)` qualifies, and negative times
matter only through the derivative at `0`. This is the convention of `IsSolution` and of the
hypothesis of `lotkaVolterra_orbitEquiv_replicator`.
