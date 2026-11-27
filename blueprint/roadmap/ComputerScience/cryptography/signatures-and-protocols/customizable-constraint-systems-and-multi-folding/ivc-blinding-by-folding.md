# Folding with a random relaxed R1CS pair hides the witness

Let $(E,u,\overline{W},x)$ with witness $(E,r_E,W,r_W)$ be any satisfying committed relaxed R1CS pair for a structure $(A,B,C)$, committed with a hiding, additively homomorphic commitment. Let $(u_{\$},w_{\$})$ be sampled by choosing $W_{\$},x_{\$},u_{\$},r_{E,\$},r_{W,\$}$ uniformly, setting $E_{\$}=AZ_{\$}\circ BZ_{\$}-u_{\$}\cdot CZ_{\$}$ for $Z_{\$}=(W_{\$},x_{\$},u_{\$})$, and committing to $E_{\$}$ and $W_{\$}$ with randomness $r_{E,\$},r_{W,\$}$. Run Nova's folding scheme on the two pairs: the prover commits to the cross term $T$ with fresh randomness $r_T$, the verifier sends $r$, and the folded witness is $W'=W+rW_{\$}$, $r'_W=r_W+r\,r_{W,\$}$, $E'=E+rT+r^{2}E_{\$}$, $r'_E=r_E+r\,r_T+r^{2}r_{E,\$}$, with $x'=x+rx_{\$}$ and $u'=u+ru_{\$}$. Then for every honest-but-curious deterministic verifier, which samples $r$ uniformly from $\mathbb{F}$, the verifier's output together with the folded witness can be simulated in expected polynomial time from the structure and the first instance alone, with indistinguishable distributions. The argument needs $r\ne0$: for $r=0$ one has $W'=W$, an event of probability $1/|\mathbb{F}|$, which is negligible when $|\mathbb{F}|$ is superpolynomial. This hiding fold is not by itself a zero-knowledge proof of a valid IVC proof: the verifier must also learn that the hidden folds were computed correctly, which HyperNova obtains by proving the folding verifier's computation in a separate circuit whose instance is itself folded with a random pair.

## Proof sketch

For $r\ne0$ the values $W',x',u',r'_W,r'_E$ are uniform because $W_{\$},x_{\$},u_{\$},r_{W,\$},r_{E,\$}$ are, and $E'$ and the folded commitments are determined by them. The simulator samples the random pair, a uniform folded pair and a challenge $r$, and solves for the commitment to the cross term from the folding equation for the error commitments; the honest verifier's challenge has the same distribution as the simulated one.

## Depends on

- [Zero-knowledge interactive proofs](../zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Relaxed R1CS instances with slack vector and scalar](../relaxed-r1cs-folding-schemes/relaxed-r1cs.md)
- [Folding scheme for an NP relation](../relaxed-r1cs-folding-schemes/folding-scheme.md)

## Proof depends on

- [Nova's folding scheme for committed relaxed R1CS](../relaxed-r1cs-folding-schemes/nova-folding-theorem.md)
- [Cross-term identity for folding relaxed R1CS](../relaxed-r1cs-folding-schemes/nova-cross-term.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573, Section 7 and Appendix D (Constructions 4 and 5, Lemma 9, Construction 6).
