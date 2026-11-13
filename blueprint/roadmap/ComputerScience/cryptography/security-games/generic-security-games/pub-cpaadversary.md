# Pub CPAAdversary

A chosen-plaintext (equivalently, eavesdropping) adversary against a public-key scheme: from
the public key it chooses two messages, and from the public key and the challenge ciphertext it
guesses. The shape of `Cslib.Crypto.PublicKey.ElGamal.Adversary`, with an arbitrary coin
distribution.
