# Cannings model of a haploid population

A **Cannings model** of a haploid population of constant size `N` is a probability law on the
parent maps `f : {0, …, N - 1} → {0, …, N - 1}` of one generation (child `c` of the new
generation has parent `f(c)` in the previous one) that is exchangeable in the children and in the
parents: the probability of `f ∘ τ` and of `σ ∘ f` equals that of `f` for all permutations `τ`
and `σ`. The [offspring vector](offspring.md) `ν_i = #{c : f(c) = i}` is then an exchangeable
vector summing to `N`, and given `ν` the children are assigned to parents uniformly at random;
this is Cannings' model (Cannings 1974). The model consists of this one-generation law only; the
iterated Cannings process uses independent copies of it for successive generations.
