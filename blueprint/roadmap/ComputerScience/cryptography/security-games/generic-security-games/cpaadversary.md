# CPAAdversary

A chosen-plaintext adversary against a private-key scheme (Katz and Lindell,
Definition 3.22): with coins `r ← coins`, the first stage `run r` has access to the encryption
oracle and outputs two challenge messages and the second stage, which receives the challenge
ciphertext, again has oracle access, and outputs a guess.
