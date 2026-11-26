# Accumulation scheme for a predicate

Let $\Phi$ be a predicate on *inputs* $q$ (for example, the expensive part of a SNARK verifier). An *accumulation scheme* for $\Phi$ consists of a generator $\mathsf{G}$, an indexer, an accumulation prover $\mathsf{P}$, an accumulation verifier $\mathsf{V}$ and a decider $\mathsf{D}$. Given inputs $q_1,\dots,q_m$ and old accumulators $\mathsf{acc}_1,\dots,\mathsf{acc}_k$, $\mathsf{P}$ outputs a new accumulator $\mathsf{acc}$ and a proof $\mathsf{pf}$. *Completeness:* if $\Phi(q_i)=1$ and $\mathsf{D}(\mathsf{acc}_j)=1$ for all $i,j$, then $\mathsf{V}(q,\mathsf{acc}_{\mathrm{old}},\mathsf{acc},\mathsf{pf})=1$ and $\mathsf{D}(\mathsf{acc})=1$. *Soundness:* for every efficient adversary producing $(q,\mathsf{acc}_{\mathrm{old}},\mathsf{acc},\mathsf{pf})$, the event that $\mathsf{V}$ and $\mathsf{D}(\mathsf{acc})$ accept while some $\Phi(q_i)=0$ or some $\mathsf{D}(\mathsf{acc}_j)=0$ has negligible probability. The scheme is useful when $\mathsf{V}$ is much cheaper than $\Phi$: the expensive check is deferred to a single final call of $\mathsf{D}$.

## Depends on

- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data from Accumulation Schemes", TCC (2020), IACR ePrint 2020/499.
- Sean Bowe, Jack Grigg, Daira Hopwood, "Recursive Proof Composition without a Trusted Setup", IACR ePrint 2019/1021 (2019).
