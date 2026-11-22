# Deterministic public-key encryption

The eavesdropping experiment for public-key encryption with a deterministic encryption function:
re-encrypting one challenge message tells which message was encrypted, so a scheme whose encryption
is injective, with two distinct eligible challenge messages for every key, has eavesdropping
advantage one half and is not secure (Katz and Lindell, Section 11.2.1).

- [Selecting the challenge message by a bit in the deterministic public-key game](pick.md)
- [Equal-length challenge pairs](equal-length.md)
- [Eavesdropping adversary with eligible challenges](eav-adversary.md)
- [Eavesdropping experiment for deterministic encryption](eav-game.md)
- [Eavesdropping advantage against deterministic encryption](eav-advantage.md)
- [Re-encryption adversary](re-encrypt.md)
- [Deterministic encryption with two distinguishable eligible messages is not eavesdropping-secure](eav-game-re-encrypt.md)
- [Deterministic encryption with two distinguishable eligible messages has eavesdropping advantage one half](eav-advantage-re-encrypt.md)
- [Injective deterministic encryption is not eavesdropping-secure on two distinct messages](eav-advantage-re-encrypt-of-injective.md)
