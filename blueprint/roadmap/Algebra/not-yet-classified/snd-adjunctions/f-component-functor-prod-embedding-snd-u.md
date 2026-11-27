# F Component Functor prod Embedding Snd unit

Let `R` and `S` be rings and let `f = (0, 1)` in `R × S`.
The unit for `fComponentFunctor ⊣ prodEmbeddingSnd R S` is
`𝟭 (ModuleCat (R × S)) ⟶ fComponentFunctor ⋙ prodEmbeddingSnd R S`.
It projects `m` to `f • m` in `fM` and then uses the identification
with the embedded component.
