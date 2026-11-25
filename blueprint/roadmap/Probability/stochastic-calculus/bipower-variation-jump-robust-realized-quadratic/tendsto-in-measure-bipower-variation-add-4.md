# Brownian increments with jumps

Assume `∀ n i, Measurable (Z n i)`, `∀ n i, μ.map (Z n i) = gaussianReal 0 1`, `Measurable K`, `∀ k, Measurable (τ k)`, `∀ k, Measurable (ξ k)` and `∀ᵐ ω ∂μ, Set.InjOn (fun k => τ k ω) (Finset.range (K ω))`.

On the grid of mesh `1/n` of `[0, 1]`, with continuous
increments `σ / √n * Z n i`, where each row `Z n` is i.i.d. standard Gaussian (for a Brownian
motion `W`, `Z n i = √n (W_{(i+1)/n} - W_{i/n})`, so the increments are those of `σ W`), plus
finitely many jumps at a.s. distinct times, which may depend on `W`, the bipower variation tends
to `(2/π) σ²` in probability: `(π/2) BPV` estimates the integrated variance `σ²` and ignores the
jumps.
