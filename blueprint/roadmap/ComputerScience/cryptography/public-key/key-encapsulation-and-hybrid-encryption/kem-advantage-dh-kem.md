# The Diffie–Hellman KEM is CPA-secure if DDH is hard

**The Diffie–Hellman KEM is CPA-secure if DDH is hard** (Katz and Lindell, Section 11.4.2),
exact form: for a uniform KDF `H` and an adversary with uniform coins, the KEM advantage is half
the DDH advantage of `kdfDist H B.guess`.
