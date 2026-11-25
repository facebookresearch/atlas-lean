# Dalal Rev

Let `σ` be a finite set of atoms with decidable equality, and represent each propositional formula over `σ` by its finite set of models (interpretations `σ → Bool`). Dalal's revision operator revises a model set `A` by a model set `B` by selecting the models of `B` that are closest to `A` in Hamming distance, namely the minimal elements of `B` for the Dalal preorder relative to `A`.
