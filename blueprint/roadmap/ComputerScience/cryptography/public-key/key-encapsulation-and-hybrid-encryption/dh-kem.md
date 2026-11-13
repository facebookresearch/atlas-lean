# Dh KEM

The **Diffie–Hellman KEM** (Katz and Lindell, Section 11.4.2) with key-derivation function
`H`: secret key `x`, public key `h = g ^ x`; encapsulation samples `y` and outputs the key
`H (h ^ y)` with encapsulation `g ^ y`; decapsulation of `e` is `H (e ^ x)`.
