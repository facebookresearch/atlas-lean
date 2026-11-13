# Forge Run

The run of the MAC forger guessing that the query with index `j` is the first bad one, on
coins `(k₁, b, r, ω₁, x, ω₂)`: it simulates the CCA experiment with challenge bit `b`, tagging
through its MAC oracle (including the challenge), and outputs the `j`-th query if it is a
decryption query (otherwise the challenge ciphertext, which loses).
