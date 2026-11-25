# Stable Steinberg Finite Weyl Torus Transport

Bounded torus transport through a weighted Weyl word.

Purpose: move one torus generator right past a head-left
`weightedWeylProd wc` word, exhibiting a left central cocycle defect and a
transported torus generator. Orientation is head-left throughout, matching
`weightedWeylProd`: the empty word fixes `(c, a', r') = (1, a, r)`, and the
cons case threads the private atomic head step through the tail recursion,
moving the recursive defect past the head Weyl factor by centrality and
combining defects in order as `c₀ * c₁`. Hypotheses: `[Field F]` only.
The transported label and coefficient are existential, and the transported
torus stays in `finiteTorusSubgroup n` by its `Fin n` endpoints.

Nonclaims: no fixed transported label or coefficient, no defect triviality,
no deletion, strict descent, or termination, no torus normal form, no kernel
generation, no TWT, and no Matsumoto theorem.
