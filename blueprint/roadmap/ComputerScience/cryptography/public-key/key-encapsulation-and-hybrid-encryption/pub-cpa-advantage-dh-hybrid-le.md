# CPA security of the ElGamal-style hybrid scheme

Let $g$ generate a finite commutative group $G$ with $|G| = q$, and consider the hybrid scheme built
from the Diffie–Hellman KEM with the identity as key derivation and the one-time-pad
data-encapsulation mechanism. Every eavesdropping adversary with uniform coins has advantage at most
the average of the DDH advantages of the two KEM adversaries built from it (with bits $1$ and $0$),
viewed as distinguishers.
