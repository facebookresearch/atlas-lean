# Completeness of Fiat–Shamir with aborts

If $\Pi$ is complete up to aborts for $\mathcal{R}$ and $(x, w) \in \mathcal{R}$, then for every hash function $H$ into the challenge set and every attempt budget $K$, every signature $(t, z)$ that the Fiat–Shamir-with-aborts signer outputs on a message $m$ (the answer of its first non-aborting attempt) verifies, i.e. the verifier of $\Pi$ accepts $(t, H(m, t), z)$. The signer and verifier are the transform $\mathsf{FS}[\mathsf{ID}, H, \kappa_m]$ of Kiltz, Lyubashevsky and Schaffner (EUROCRYPT 2018, Section 3.1) with $\kappa_m = K$, and completeness up to aborts is the first condition of their Definition 2.3.

## Proof sketch

An output $(t, z)$ comes from an attempt that computed an honest commitment $t$ with state, the challenge $c = H(m, t)$, and an honest answer $z \ne \bot$ on $c$. Completeness up to aborts says the verifier of $\Pi$ accepts every such non-aborting transcript $(t, c, z)$, and verification recomputes exactly this $c$ from $m$ and $t$, so it accepts. The argument uses nothing about $H$ or $K$. The same holds for the variant used in the random oracle analysis, which runs all $K$ attempts and outputs the first non-aborting one: it makes at most $K$ hash queries (one per attempt), and for a fixed $H$ its output depends only on the attempts up to the first success, which are distributed as in the signer that stops there, so the two signers have the same output law.

## Depends on

- [Fiat–Shamir with aborts signatures](fiat-shamir-with-aborts-signatures.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, LNCS 7237, 2012, Fig. 1 (the signing loop that restarts on rejection and outputs only an accepted attempt).
- Eike Kiltz, Vadim Lyubashevsky and Christian Schaffner, "A Concrete Treatment of Fiat-Shamir Signatures in the Quantum Random-Oracle Model", Advances in Cryptology – EUROCRYPT 2018, LNCS 10822, 2018, Definition 2.3 (every transcript with $Z \ne \bot$ is valid) and Section 3.1 (the transform $\mathsf{FS}[\mathsf{ID}, H, \kappa_m]$ and its verification).
