# Upwind Face Flux

Upwind face flux through face `i`, the face between cell `i - 1` and cell `i`, positive
toward increasing index: the cross-section `area` times the advective flux `v c` taken on the
upstream side, `max v 0 * c (i - 1) + min v 0 * c i`.

The cells are indexed by $\mathbb{Z}/n\mathbb{Z}$: periodic with wraparound for $n > 0$, and the integer lattice for $n = 0$ (see [the conservative step](is-conservative-step.md)).
