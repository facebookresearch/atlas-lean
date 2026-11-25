# Chosen-ciphertext adversary against public-key encryption

A chosen-ciphertext adversary against a public-key encryption scheme (Katz and Lindell,
Definition 11.8) draws random coins from a distribution of its own and runs in two stages, both of
which see the public key and have access to a decryption oracle. The first stage outputs two
challenge messages; the second, which may depend on everything the first saw, receives the challenge
ciphertext and outputs a guess.
