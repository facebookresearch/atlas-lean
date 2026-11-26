# Post-quantum security of Kilian's succinct arguments

Let $\mathrm{Kilian}[\mathrm{PCP},\mathrm{VC}]$ be Kilian's four-message public-coin argument, in which the prover commits to a PCP string with a vector commitment (e.g., a Merkle tree) and opens the locations queried by the PCP verifier. If $\mathrm{PCP}$ has negligible soundness error and $\mathrm{VC}$ is a collapsing vector commitment (obtainable from collapsing hash functions, e.g., from post-quantum LWE), then $\mathrm{Kilian}[\mathrm{PCP},\mathrm{VC}]$ is a post-quantum succinct argument: no quantum polynomial-time prover convinces the verifier on a false instance with non-negligible probability. Soundness alone does not give extraction, since a convincing PCP string need not reveal an NP witness. If moreover $\mathrm{PCP}$ is a PCP of knowledge, i.e. has a polynomial-time extractor $E$ and negligible knowledge error $\kappa_{\mathrm{PCP}}$ ($E(x,\pi)$ outputs a witness for $x$ whenever $\pi$ is accepted with probability greater than $\kappa_{\mathrm{PCP}}$), then $\mathrm{Kilian}[\mathrm{PCP},\mathrm{VC}]$ is a post-quantum succinct argument of knowledge with negligible knowledge error. In the QROM, Micali's non-interactive CS proofs built from a PCP with negligible soundness error are likewise sound against quantum adversaries.

## Proof sketch

The obstacle is rewinding a quantum prover across many challenges, since measuring openings disturbs its state. Kilian's protocol is not $k$-special sound for any $k$, so special-soundness rewinding does not apply. The proof develops a state-repair procedure (based on Marriott–Watrous amplification and collapsing) that restores the prover's success probability after each measured opening; for a collapsing protocol this yields many accepting transcripts with distinct challenges, from which the extractor assembles a PCP string $\pi$ accepted with probability $\Omega(\varepsilon)$ when the prover convinces with probability $\varepsilon$. A sound PCP then forces $\varepsilon$ to be negligible on false instances; a PCP of knowledge additionally turns $\pi$ into a witness via $E(x,\pi)$. In the QROM, compressed-oracle techniques bound the probability of inconsistent Merkle openings.

## Depends on

- [Collapsing hash functions and collapse-binding commitments](collapsing-hash.md)
- [The quantum random oracle model](quantum-random-oracle-model.md)
- [Succinct arguments and SNARKs](../../signatures-and-protocols/zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)
- [Knowledge soundness](../../signatures-and-protocols/zero-knowledge-and-arguments/knowledge-soundness.md)

## Proof depends on

- [Random oracles and LWE-based hashes are collapsing](collapsing-from-random-oracle-and-lwe.md)
- [Succinct arguments from probabilistically checkable proofs](../../signatures-and-protocols/zero-knowledge-and-arguments/succinct-arguments-from-probabilistically.md)

## Sources

- Alessandro Chiesa, Fermi Ma, Nicholas Spooner, Mark Zhandry, "Post-Quantum Succinct Arguments: Breaking the Quantum Rewinding Barrier", FOCS (2021), Theorems 5.1 and 7.1, arXiv:2103.08140.
- Alessandro Chiesa, Peter Manohar, Nicholas Spooner, "Succinct Arguments in the Quantum Random Oracle Model", TCC (2019).
