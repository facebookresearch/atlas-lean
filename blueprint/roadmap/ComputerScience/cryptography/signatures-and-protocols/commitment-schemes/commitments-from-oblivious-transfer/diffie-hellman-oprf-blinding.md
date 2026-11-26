# Correctness and blinding laws of the Diffie–Hellman OPRF protocols

In the Diffie–Hellman OPRF protocols over a group of prime order $q$: (i) *correctness*: if the sender answers honestly, the receiver's unblinded group element is $H(x)^k$, so it outputs $F'(k, x)$; (ii) *receiver privacy*: in OPRF1, for uniform $\rho \in \mathbb{Z}_q^*$ the message $H(x)^\rho$ is uniform on $\mathbb{G} \setminus \{1\}$ when $H(x) \ne 1$, and hashed inputs differing by an invertible exponent induce the same message distribution; in OPRF2 the message $H(x)^\rho g^\tau$ with uniform $\tau$ is uniform on $\mathbb{G}$ and independent of $x$; (iii) *effect of a deviating sender*: if the sender answers $v^k \cdot \delta$ for some $\delta \ne 1$, then in OPRF2 the receiver's unblinded element is $H(x)^k \cdot \delta^{1/\rho}$, and $\delta^{1/\rho}$ is uniform on $\mathbb{G}\setminus\{1\}$, independent of $x$, so a deviating sender cannot bias the output in an input-dependent way.

## Proof sketch

All claims are exponent arithmetic in a group of prime order: $(H(x)^{\rho k})^{1/\rho} = H(x)^k$, and multiplication by a uniform independent exponent or group element is a bijection preserving the uniform law.

## Depends on

- [Diffie–Hellman oblivious pseudorandom functions](diffie-hellman-oprf.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
