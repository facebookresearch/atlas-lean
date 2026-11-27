# The CPA experiment, eagerly sampled

For finite nonempty types of keys, adversary coins and encryption randomness, a scheme with uniform keys whose encryption
applies a deterministic algorithm `e k m` to uniform randomness, and an adversary with uniform
coins making at most `q` queries, the left-or-right experiment `cpaExp` samples the key, the
coins, the `q` encryption randomness values and the challenge randomness up front.
