# Is Fluctuation Path

`U` solves the **linear fluctuation equation** on `[0, T]` driven by the path `m`, with
initial value `u₀`, around the deterministic path `x`:
`U(t) = u₀ + (m(t) - m(0)) + ∫₀ᵗ DF(x(s)) U(s) ds`, and `U` is continuous on `[0, T]`. The
driving path enters only through its increments, so `U(0) = u₀` for every `m`
(`IsFluctuationPath.initial`). With `m` the Gaussian martingale of the module docstring, which
starts at `0`, this is the Ornstein–Uhlenbeck-type SDE `dU = DF(x(t)) U dt + dM(t)` of the
diffusion approximation, solved pathwise.
