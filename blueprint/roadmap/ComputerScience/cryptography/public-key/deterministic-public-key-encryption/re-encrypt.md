# Re Encrypt

The **re-encryption adversary** against a deterministic scheme (Katz and Lindell,
Section 11.2.1): it submits the eligible messages `msgs pk` (eligibility is `hel`), encrypts the
second one itself, and guesses `true` exactly when the challenge ciphertext equals that
encryption. It uses no coins.
