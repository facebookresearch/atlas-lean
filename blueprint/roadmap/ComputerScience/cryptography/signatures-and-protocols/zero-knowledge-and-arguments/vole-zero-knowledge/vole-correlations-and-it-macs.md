# Vector oblivious linear evaluation and IT-MACs

Let $R$ be a finite commutative ring, such as a finite field $\mathbb{F}_q$, an extension field $\mathbb{F}_{2^\lambda} \supseteq \mathbb{F}_2$, or $\mathbb{Z}_n$; finiteness is what makes the uniform sampling below well defined. A *VOLE correlation* of length $n$ gives the sender (prover) vectors $u, v \in R^n$ and the receiver (verifier) a global key $\Delta \in R$ and $q \in R^n$ such that

$$
q = v + u\,\Delta .
$$

The ideal VOLE functionality samples $u, v \in R^n$ and $\Delta \in R$ uniformly from these finite sets and hands out the two shares; a cached ideal world answers repeated requests of either role with the same correlation. A value $x$ is *authenticated* by an *information-theoretic MAC* (IT-MAC) when the prover holds $(x, m_x)$ and the verifier holds the key $k_x = m_x + x\Delta$; the prover commits to a witness $x$ by sending the correction $d = x - u$, after which both sides update to an IT-MAC on $x$. Linear combinations of authenticated values are authenticated locally, and an opening of $x$ is checked by $k_x = m_x + x\Delta$.

## Sources

- Elette Boyle et al., "Efficient Two-Round OT Extension and Silent Non-Interactive Secure Computation", Proceedings of the 2019 ACM SIGSAC Conference on Computer and Communications Security (CCS 2019), 2019.
- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
- Kang Yang, Pratik Sarkar, Chenkai Weng and Xiao Wang, "QuickSilver: Efficient and Affordable Zero-Knowledge Proofs for Circuits and Polynomials over Any Field", Proceedings of the 2021 ACM SIGSAC Conference on Computer and Communications Security (CCS 2021), 2021.
