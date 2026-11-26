# Winslett's possible models update

Let `σ` be a finite set of atoms with decidable equality, and represent each propositional formula over `σ` by its finite set of models (interpretations `σ → Bool`). Winslett's possible models approach (Katsuno–Mendelzon, §3.1) updates a model set `A` by a model set `B` as follows: each model `I` of `A` selects the `≤_{I,pma}`-minimal elements of `B` (KM's `Incorporate(Mod(μ), I)`), and the update is the union of these selections over all models of `A`.
