# Legendre-transform symmetry for chord currents

For a [valid](valid.md) [Schnakenberg network](schnakenberg-network.md) on a finite nonempty state
space, every initial state `ω₀` and every `α`, the Legendre transform [`H`](h.md) of the
chord-current generating function [`Q`](q.md) satisfies `H(-α) = H(α) + 𝒜·α` in `[-∞, ∞]`, where
`𝒜_l` is the [affinity](affinity.md) of the fundamental cycle of chord `l`; that is,
`H(-α) - H(α) = ∑_l 𝒜_l α_l` where finite.

This is the chord-current analogue of equation (73) of Andrieux and Gaspard (2007), which is stated
there for grouped currents. It follows from the [symmetry `Q(λ) = Q(𝒜 - λ)`](q-symm.md) of their
equation (39) by the Legendre transform of their equation (72). It is an identity for the transform
of `Q` and makes no statement about probabilities.

## Depends on

- [Schnakenberg Network](schnakenberg-network.md)
- [Valid](valid.md)
- [Affinity](affinity.md)
- [Legendre transform of `Q`](h.md)

## Proof depends on

- [Existence and symmetry of the current generating function](q-symm.md)
- [`H` as a supremum](h-eq-i-sup.md)

## Sources

- D. Andrieux and P. Gaspard, "Fluctuation theorem for currents and Schnakenberg network theory",
  Journal of Statistical Physics 127 (2007) 107–131, arXiv:cond-mat/0512254 (v3), equations (39),
  (72) and (73).
