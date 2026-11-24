# With a dry neighbour, wet-state consistency does not give the balance

Strict wetness cannot be relaxed to a free surface that touches the higher bed. Let `g` be real and
`zL < zR`, and take the lake at rest with `η = zR`: a left cell of depth `zR - zL` at rest beside a
dry right cell (depth `0`, velocity `0`). There is a numerical flux `𝓕` that is consistent on wet
states: `𝓕((h, h u), (h, h u)) = (h u, h u² + g h² / 2)` for every depth `h > 0` and velocity `u`,
but whose [left numerical flux](left-flux.md) has momentum component different from
`g (zR - zL)² / 2`: both reconstructed states are the dry state `(0, 0)`, about which consistency on
wet states says nothing. A flux consistent also at the dry state, as in the source's Theorem 2.1,
balances at this endpoint.
