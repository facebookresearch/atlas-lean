# Textbook RSA is not eavesdropping-secure

**Textbook RSA is not eavesdropping-secure** (Katz and Lindell, Sections 11.2.1 and 11.5.1):
for every distribution `gen` of RSA keys, the adversary that submits the equal-length messages `1`
and `-1`, re-encrypts `-1` under the public key and compares, has eavesdropping advantage `1/2`.
Both messages are units (`attackMsgs_isUnit`), so this holds for the textbook scheme on `Z*_N`
(Section 11.5.1), not only for the broader all-residue model `ZMod n` of `RSA.lean`. By
Proposition 11.3 of Katz and Lindell (CPA security implies eavesdropping security), textbook RSA
is therefore not CPA-secure either; that step is not formalized here.
