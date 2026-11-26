# Completeness of Fiat–Shamir with aborts

If $\Pi$ is complete up to aborts for $\mathcal{R}$ and $(x, w) \in \mathcal{R}$, then for every hash function $H$ (fixed or random), every signature produced by the Fiat–Shamir-with-aborts signer with any attempt budget $K$ verifies. The all-attempt signer makes at most $K$ hash queries, and with a fixed hash its output law coincides with that of the signer that stops at the first success.

## Proof sketch

Each non-aborting attempt outputs an accepting transcript of $\Pi$ with challenge $H(m,t)$, which is exactly what verification checks.

## Depends on

- [Fiat–Shamir with aborts signatures](fiat-shamir-with-aborts-signatures.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
