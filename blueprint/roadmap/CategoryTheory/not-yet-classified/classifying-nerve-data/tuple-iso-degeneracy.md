# Tuple Iso degeneracy

Degeneracy compatibility of the degreewise equivalence.

Both sides insert `1` head-first; the bar side uses `barEtaAtPos` with
`tensorMonad_eta_app`, the nerve side uses the pinned nerve degeneracies with
`SingleObj.id_as_one`. `Fin.rev` is never unfolded beyond the accepted
`barEtaAtPos_rev` wrapper.
