# The binding experiment

For a keyed commitment scheme with key generation $\mathrm{Gen}$, the binding experiment (Katz and
Lindell, Section 5.6.5) draws a key $k \leftarrow \mathrm{Gen}$ and the adversary's coins, and outputs
$1$ when the adversary's output opens one commitment of the scheme with key $k$ to two different
messages. Neither the key nor the coins need be uniform.
