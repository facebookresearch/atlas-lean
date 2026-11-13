# Bad-event bound from one-wayness

Composing `winProb_forgeGame_le` with Lamport's
reduction (`Lamport.forgeGame_le`, Katz and Lindell, Theorem 12.16), the forgery probability is at
most `N · 2 ℓ` times the success probability of an inverter for `f`, plus the key-mismatch event.
As for `winProb_forgeGame_le`, that term is not bounded by a collision-finding advantage, so this is
not EUF security from one-wayness and collision resistance.
