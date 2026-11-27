# Public-coin interactive oracle proofs

A $k$-round *public-coin interactive oracle proof* (IOP) for a relation $\mathcal{R}$ over an alphabet $\Sigma$ consists of a prover and a verifier. In round $i$ the prover sends an *oracle* $\pi_i \in \Sigma^{\ell_i}$ (a string the verifier may query) and the verifier replies with a uniformly random challenge $c_i$ from a finite set; after the last round the verifier queries a few positions of the oracles and accepts or rejects. It is *complete* if for $(x, w) \in \mathcal{R}$ the honest prover is always accepted. It is *round-by-round sound* with errors $(\varepsilon_i)$ if there is a predicate *doomed* on partial transcripts such that the empty transcript is doomed for every $x$ outside the language, a doomed transcript stays doomed after any prover message and the next challenge except with probability $\varepsilon_i$ (escape), and full doomed transcripts are rejected except with the query-phase error. Round-by-round soundness implies soundness with error $\sum_i \varepsilon_i + \varepsilon_{\mathrm{query}}$ against every prover, where $\varepsilon_{\mathrm{query}}$ is the query-phase error.

## Depends on

- [Zero-knowledge interactive proofs](../zero-knowledge-interactive-proofs.md)
- [Probabilistically checkable proofs](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pcp.md)

## Sources

- Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner, "Interactive Oracle Proofs", Theory of Cryptography – TCC 2016-B, Part II, 2016.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
