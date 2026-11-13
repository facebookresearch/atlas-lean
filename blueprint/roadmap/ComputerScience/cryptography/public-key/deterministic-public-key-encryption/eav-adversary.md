# Eav Adversary

An eavesdropping adversary against a public-key scheme with public keys `PK`, message types
`M pk` and ciphertext types `C pk`, with random coins in `R`, whose challenge pairs must satisfy
the eligibility relation `Eligible` (equal length in Katz and Lindell, Section 11.2.1): from the
public key it chooses two eligible messages, and from the public key and the challenge ciphertext
it guesses which one was encrypted.

Wave 2: migrate to `CSLibExt.Crypto.Framework` games.
