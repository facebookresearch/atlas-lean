# Completeness, abort probability and zero knowledge of Lyubashevsky's protocol

In Lyubashevsky's identification protocol with $\|S\|_\infty \le \eta$ and $k\eta \le \beta \le \gamma$: (i) every non-aborting answer of the honest prover is accepted, for every witness with $AS = T$; (ii) at every challenge the prover aborts with probability exactly

$$
1 - \left(\frac{2(\gamma - \beta) + 1}{2\gamma + 1}\right)^{m} \;\le\; \frac{2 m \beta}{2\gamma + 1};
$$

(iii) conditioned on not aborting, the response $z$ is uniform on $[-(\gamma - \beta), \gamma - \beta]^m$ and independent of $S$, so a simulator that samples $z$ uniformly from this box, sets $t = Az - Tc$, and aborts with the same probability reproduces the accepted view exactly (non-abort special HVZK).

## Proof sketch

Since $\|Sc\|_\infty \le k\eta \le \beta$, for every target $z$ in the inner box exactly one mask $y = z - Sc$ in the outer box produces it, so the accepted response is uniform on the inner box and the acceptance probability is the ratio of the box sizes. Bernoulli's inequality gives the linear bound.

## Depends on

- [Lyubashevsky's lattice identification protocol](lyubashevsky-identification.md)

## Proof depends on

- [Zero knowledge up to aborts](zero-knowledge-up-to-aborts.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
