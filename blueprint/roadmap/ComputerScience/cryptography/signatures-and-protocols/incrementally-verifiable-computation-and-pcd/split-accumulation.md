# Split accumulation and NARKs with accumulation

An accumulation scheme is *split* if every accumulator is a pair $\mathsf{acc}=(\mathsf{acc.x},\mathsf{acc.w})$ of a short instance part and a possibly long witness part, inputs are likewise split $q=(q.\mathsf{x},q.\mathsf{w})$, and the accumulation verifier $\mathsf{V}$ reads only the instance parts $q.\mathsf{x}$, $\mathsf{acc}_j.\mathsf{x}$, $\mathsf{acc.x}$ and the proof $\mathsf{pf}$; only the decider reads the witness part. A *NARK with split accumulation* is a non-interactive argument whose proofs need not be succinct, together with a split accumulation scheme for its verifier, in which the short instance part of each proof suffices for the accumulation verifier.

## Depends on

- [Accumulation scheme for a predicate](accumulation-scheme.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, William Lin, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data without Succinct Arguments", CRYPTO (2021), IACR ePrint 2020/1618.
