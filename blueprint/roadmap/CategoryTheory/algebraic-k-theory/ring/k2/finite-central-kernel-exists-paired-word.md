# Stable Steinberg Finite Weyl Kernel Paired Word

Finite central-kernel elements yield paired words with trivial label product.

Purpose: formal paired-word bridge for the Matsumoto comparison: from
`g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n` over `[Field F]`,
exhibit `wc : List (SwapLabel n × Fˣ)` with `g = weightedWeylProd wc` and
`wordProd (wc.map Prod.fst) = 1`. Orientation is head-left throughout,
matching `weightedWeylProd`, `wordProd`, and the accepted `List.ofFn` order.
The empty word gives `1 = 1 ∧ wordProd [] = 1`, uniform in ranks `n = 0, 1`.

Nonclaims: bridge only; no finite-torus containment, kernel generation,
`ker ⊓ finiteStage`, TWT, inverse, naturality, normal-form, or Matsumoto claim.
