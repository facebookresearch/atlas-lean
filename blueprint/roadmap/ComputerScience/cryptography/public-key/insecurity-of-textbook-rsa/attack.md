# Attack

The eavesdropping attack on textbook RSA (Katz and Lindell, Section 11.2.1): submit the units
`1` and `-1` (valid plaintexts of the textbook scheme on `Z*_N`, and an eligible pair, since
`ZMod n` is a fixed-length message space), re-encrypt `-1` under the public key, and compare with
the challenge.
