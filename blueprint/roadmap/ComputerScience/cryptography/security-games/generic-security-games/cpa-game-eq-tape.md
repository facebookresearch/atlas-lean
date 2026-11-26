# The CPA game, eagerly sampled

Let the key space `K`, the adversary coins `R` and the encryption randomness
`Rnd` be finite and nonempty. Suppose the scheme `S` generates a uniform key
and encrypts by applying a deterministic algorithm `e k m` to uniform
randomness, and the adversary `A` has uniform coins and makes at most `q`
encryption queries. Then the CPA game of `S` against `A` is the probability
that a deterministic test succeeds on one uniform sample `(k, b, r, ρ, rs)` of
a key, a challenge bit, the adversary's coins, `q` encryption randomness
values and the challenge randomness: the guess of `A` computed with this
sample equals `b`.
