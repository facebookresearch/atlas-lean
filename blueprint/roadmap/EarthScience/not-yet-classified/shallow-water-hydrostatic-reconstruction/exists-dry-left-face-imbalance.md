# Dry state excluded

Strict wetness cannot be relaxed to a free
surface that touches the higher bed, for numerical fluxes assumed
consistent only on wet states. For every `g` and every step
`zL < zR`, take the lake at rest with `η = zR`: a wet left cell of depth
`zR - zL` at rest beside a dry right cell. Some numerical flux that is
consistent on every wet state gives a corrected left momentum flux
different from `g * (zR - zL) ^ 2 / 2`, because both reconstructed
states are the dry state `(0, 0)`, about which consistency on wet states
says nothing. A flux consistent also at the dry state, as in the
source's Theorem 2.1, balances at this endpoint.
