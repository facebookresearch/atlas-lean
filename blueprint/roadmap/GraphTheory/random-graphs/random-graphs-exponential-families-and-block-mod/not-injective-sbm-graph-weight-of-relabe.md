# Not injective sbm Graph Weight of relabel ne

Assume that `K` is finite and that `V` is finite. Assume `(p ∘ σ, fun i j => W (σ i) (σ j)) ≠ (p, W)`.

Label swapping makes the weight map non-injective.

In symbols: `¬ Function.Injective (fun θ : (K → ℝ) × (K → K → ℝ) => sbmGraphWeight (V`.
