# Pub Oracle CPAAdversary

A chosen-plaintext adversary against a public-key scheme **with an encryption oracle**
(Katz and Lindell, Section 11.2.2): with coins `r ← coins`, the first stage sees the public key
and has access to `Enc_pk(·)`, and outputs two challenge messages and the second stage, which
receives the challenge ciphertext and again has oracle access.
