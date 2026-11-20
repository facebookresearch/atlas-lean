# Deterministic public-key encryption

The eavesdropping experiment for public-key encryption with a deterministic encryption function:
re-encrypting one challenge message tells which message was encrypted, so a scheme whose encryption
is injective, with two distinct eligible challenge messages for every key, has eavesdropping
advantage one half and is not secure (Katz and Lindell, Section 11.2.1).

- [Selecting the challenge message by a bit in the deterministic public-key game](pick.md)
