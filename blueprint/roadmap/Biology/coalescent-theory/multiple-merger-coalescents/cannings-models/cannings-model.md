# Cannings Model

A **Cannings model** of a haploid population of constant size `N`, as the law of one
generation's parent map: child `c` of the new generation has parent `f c` in the previous one.
The law is exchangeable in the children (relabelling the children `f ↦ f ∘ τ`) and in the
parents (relabelling the parents `f ↦ σ ∘ f`). The offspring vector `ν_i = #{c | f c = i}`
(`offspring`) is then an exchangeable vector summing to `N`, and given `ν` the children are
assigned to parents uniformly at random; this is Cannings' model (Cannings 1974). Successive
generations are independent copies of this law. Real-valued probabilities use the masses
`(law f).toReal`.
