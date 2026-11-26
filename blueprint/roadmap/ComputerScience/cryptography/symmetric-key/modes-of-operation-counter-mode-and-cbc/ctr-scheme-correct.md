# Correctness of counter mode

Let `N ≠ 0`, the key space `K` be finite and nonempty and the blocks `Y` an additive
group. For every keyed function `F : K → ZMod N → Y`, counter mode with `ℓ`-block messages
is correct: decrypting any encryption of a message `m` under a key `k` returns `m`.
