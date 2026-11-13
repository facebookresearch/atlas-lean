# Eligible

The challenge-pair eligibility relation for textbook RSA: every pair is eligible. The
equal-length condition of `PubK^eav` (Katz and Lindell, Section 11.2.1) holds for every pair
because RSA messages are elements of `ZMod n`, a fixed-length message space (every message is
encoded with the bit length of `n`).
