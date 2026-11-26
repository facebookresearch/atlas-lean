# Zero-knowledge IVC proofs by folding with a random satisfying instance

Let $(U,W)$ be a satisfying committed relaxed R1CS pair produced by an IVC prover, and let $(U_{\$},W_{\$})$ be a uniformly random satisfying committed relaxed R1CS pair for the same structure (sampled by choosing $W_{\$}$ and $u_{\$}$ uniformly and setting $E_{\$}$ to make the relation hold). If the commitment scheme is perfectly hiding and the folding scheme is applied with the folded commitments rerandomized, then the folded pair $(U',W')$ obtained by folding $(U,W)$ with $(U_{\$},W_{\$})$ at challenge $r$ is distributed independently of $W$ given $U'$ and the public folding transcript. Hence publishing the folded pair and the transcript, instead of $(U,W)$, gives an IVC proof that reveals nothing about the step witnesses.

## Proof sketch

The folded witness is $W+rW_{\$}$ with $W_{\$}$ uniform, hence uniform for $r\ne 0$; the folded error $E+rT+r^{2}E_{\$}$ is then determined by the relation from the folded witness and $u'$. With perfectly hiding commitments the transcript's commitments are independent of the openings, so a simulator samples the folded pair directly.

## Depends on

- [Nova's folding scheme for committed relaxed R1CS](../relaxed-r1cs-folding-schemes/nova-folding-theorem.md)
- [Zero-knowledge interactive proofs](../zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)

## Proof depends on

- [Cross-term identity for folding relaxed R1CS](../relaxed-r1cs-folding-schemes/nova-cross-term.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573.
