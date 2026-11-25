# Stable Steinberg Finite Weyl Hurwitz Global Decrease

One-step global weighted Hurwitz strict decrease.

Purpose: from a coefficient-carrying Weyl word whose label projection is
nonempty with permutation product one, produce a shorter paired word with
product-one projection and exact two-letter length drop, keeping head-left
orientation throughout (matching `weightedWeylProd`). Hypotheses: `[Field F]`
only, a paired word `wc`, nonemptiness of the label projection itself, and
product one of that projection. The shortened word, the cocycle defect in
`torusCocycleSubgroup`, and the transported torus residual in
`finiteTorusSubgroup n` are existential. The defect order is the canonical
temporal order inherited from the deletion-transport packet.

Nonclaims: one step only, not the normal-form induction; no exposed `pre`,
`suf`, trace, or auxiliary midpoint word; no kernel generation, `List.ofFn`
bridge, TWT, inverse identities, naturality, or Matsumoto claim.
