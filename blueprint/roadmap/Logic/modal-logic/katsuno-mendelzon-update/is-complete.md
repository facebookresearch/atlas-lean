# Complete belief sets

Let `σ` be a finite set of atoms with decidable equality, and represent each propositional formula over `σ` by its finite set of models (interpretations `σ → Bool`). A model set `A` is complete (Katsuno–Mendelzon, §2) if for every sentence `C` it implies `C` or implies `¬C`, that is `A ⊆ C` or `A ⊆ Cᶜ`. In particular the empty (inconsistent) model set is complete.
