# The binding experiment

**The binding experiment** for the keyed commitment scheme `S` with key generation `gen`
(Katz and Lindell, Section 5.6.5): `k ← gen`, `r ← A.coins`, and the experiment outputs `1` when
`A.run k r` opens one commitment of `S k` to two different messages.
