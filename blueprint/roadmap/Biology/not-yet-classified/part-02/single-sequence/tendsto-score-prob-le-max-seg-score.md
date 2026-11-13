# The maximal segment score grows without bound

**The maximal segment score grows without bound** as soon as positive scores have positive
probability: `P(Mₙ ≥ t) → 1` for every `t`. Under negative drift the walk maximum itself stays
tight (`scoreProb_le_walkMax_le`); the growth rate `Mₙ / log n → 1 / θ` is not proved here (see
Karlin and Dembo 1992).
