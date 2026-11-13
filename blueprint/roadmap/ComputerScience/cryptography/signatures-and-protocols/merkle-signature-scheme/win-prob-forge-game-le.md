# Forgery bound up to the key-mismatch event

**Forgery bound up to the key-mismatch event** (an intermediate bad-event bound, not EUF
security): for `ℓ ≥ 1` and `N ≥ 1`, the forgery probability against the `N`-key stateful signer is
at most `N` times the success probability of the Lamport one-time forger `reduction N F`, plus the
probability of the key-mismatch event `keyMismatchGame`, in which the forger's signature carries a
Lamport key other than the honest one at its index. That term is the forger's own bad-event
probability, not a collision finder's advantage: each run in it exhibits a collision of `h` or `H`
(`collision_of_keyMismatchGame`), but no collision finder is constructed, and for compressing
hashes collisions exist, so this theorem alone does not give EUF security under collision
resistance. The factor `N` is the guess of the forgery's index (Katz and Lindell, Section 12.6,
for one-time signatures and hash trees).
