# ElGamal eavesdropping experiment as public-key CPA

For every eavesdropping adversary `A` with uniform coins against ElGamal with
an element `g` of a commutative group `G` and exponents modulo `q ≠ 0`, the ElGamal eavesdropping experiment
of `A` equals the public-key experiment `PubK^eav` of the ElGamal scheme
against the embedded adversary `A.toPubCPA`, whose underlying ElGamal
adversary is `A` itself (Katz and Lindell, Definition 11.2).
