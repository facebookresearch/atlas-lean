# Junction-local receiving constraint of a turning certificate

Let `V` (junctions), `E` (links) and `C` (commodities) be types, `E` and `C` finite, each link `e`
running from junction `tail e` to junction `head e`, and let `q(c, e, e')` be a turning certificate:
the flow of commodity `c` from link `e` into link `e'` during one time step. The certificate
satisfies the junction-local receiving constraint when, for every link `e'`, the turning flows into
`e'` from the links ending at `tail e'`, summed over commodities, are at most the
[receiving supply](supply.md) `min(w (kj - k), vf w kj / (vf + w))` of the first cell of `e'`, with
that link's free-flow speed `vf`, wave speed `w`, jam density `kj` and first-cell density `k`. With
the convention `x / 0 = 0` the capacity term is `0` when `vf + w = 0`. No sign condition is imposed;
for `vf > 0`, `w > 0` and `0 ≤ k ≤ kj` the supply is nonnegative, and outside that domain the
constraint can be unsatisfiable.
