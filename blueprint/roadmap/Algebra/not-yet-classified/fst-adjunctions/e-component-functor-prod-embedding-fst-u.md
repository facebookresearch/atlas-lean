# E Component Functor prod Embedding Fst unit

Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`.
The unit for `eComponentFunctor ⊣ prodEmbeddingFst R S` is
`𝟭 (ModuleCat (R × S)) ⟶ eComponentFunctor ⋙ prodEmbeddingFst R S`.
It projects `m` to `e • m` in `eM` and then uses the identification
with the embedded component.
