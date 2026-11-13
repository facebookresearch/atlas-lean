# Encrypt-then-MAC has ciphertext integrity

**Encrypt-then-MAC has ciphertext integrity** (Katz and Lindell, Section 4.5): for every
ciphertext forger making at most `q` encryption queries, its advantage is at most the
existential-forgery advantage of `ctxtReduction` against the MAC. No guessing factor: a fresh
valid ciphertext is a valid tag on a never-tagged value.
