# Security of the Fiat–Shamir transformation in the quantum random oracle model

Let $\Sigma$ be a three-move public-coin interactive proof (a $\Sigma$-protocol) and let $\mathrm{FS}[\Sigma]$ be its Fiat–Shamir transform with a quantum random oracle. If $\Sigma$ has soundness error $\epsilon$ against quantum provers, then $\mathrm{FS}[\Sigma]$ has soundness error at most $(2q+1)^{2}\epsilon$ against $q$-query quantum provers in the QROM. If $\Sigma$ is a quantum proof of knowledge (e.g., special sound with collapsing responses), then $\mathrm{FS}[\Sigma]$ is a quantum argument of knowledge, and Fiat–Shamir signatures from such identification schemes are EUF-CMA secure in the QROM (with known polynomial losses). Independently, Liu–Zhandry proved QROM security of Fiat–Shamir signatures from lossy identification and from collapsing Sigma protocols via compressed-oracle rewinding.

## Proof sketch

Apply the measure-and-reprogram lemma: a successful non-interactive prover outputting $(\mathsf{com},\mathsf{resp})$ with $V(\mathsf{com},H(\mathsf{com}),\mathsf{resp})$ yields an interactive prover that sends the measured $\mathsf{com}$, receives a uniformly random challenge (playing the reprogrammed $\Theta$) and outputs the response, with success probability reduced by at most $(2q+1)^{2}$. Knowledge soundness follows by combining this with quantum rewinding for collapsing protocols.

## Depends on

- [Security of the Fiat–Shamir transform](../../signatures-and-protocols/zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)
- [Zero-knowledge interactive proofs](../../signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [The quantum random oracle model](quantum-random-oracle-model.md)

## Proof depends on

- [Measure-and-reprogram for quantum random oracles](measure-and-reprogram.md)

## Sources

- Jelle Don, Serge Fehr, Christian Majenz, Christian Schaffner, "Security of the Fiat-Shamir Transformation in the Quantum Random-Oracle Model", CRYPTO (2019), arXiv:1902.07556.
- Qipeng Liu, Mark Zhandry, "Revisiting Post-Quantum Fiat-Shamir", CRYPTO (2019), IACR ePrint 2019/262.
