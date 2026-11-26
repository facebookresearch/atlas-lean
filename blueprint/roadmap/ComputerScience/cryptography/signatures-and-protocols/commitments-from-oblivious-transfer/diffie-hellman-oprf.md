# Diffie–Hellman oblivious pseudorandom functions

Let $\mathbb{G}$ be a cyclic group of prime order $q$ with generator $g$, $H : X \to \mathbb{G}$ and $H' : X \times \mathbb{G} \to Y$ hash functions. The *Diffie–Hellman PRF* is $F'(k, x) = H'(x, H(x)^k)$ with key $k \in \mathbb{Z}_q$. An *oblivious PRF protocol* lets a receiver with input $x$ learn $F'(k, x)$ from a sender holding $k$ while the sender learns nothing about $x$. In protocol OPRF1 the receiver sends $v = H(x)^\rho$ for uniform $\rho \in \mathbb{Z}_q^*$, the sender returns $w = v^k$, and the receiver outputs $H'(x, w^{1/\rho})$. In protocol OPRF2 the receiver sends $v = H(x)^\rho g^\tau$ and, given the sender's public key $g^k$, unblinds $w$ as $(w \cdot (g^k)^{-\tau})^{1/\rho}$.

## Depends on

- [DDH advantage of the distinguisher built from a CDH solver](../../public-key/hardness-assumptions/ddh-advantage-ddh-of-cdh.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
