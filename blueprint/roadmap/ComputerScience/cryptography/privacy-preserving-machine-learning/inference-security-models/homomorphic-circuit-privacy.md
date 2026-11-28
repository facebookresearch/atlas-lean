# Statistical circuit privacy of homomorphic evaluation

A homomorphic encryption scheme is *(statistically) circuit private* for a circuit class when, for every generated key pair, evaluating any admitted circuit on any fixed valid input ciphertexts yields a ciphertext statistically indistinguishable from a fresh encryption of the circuit's output, while evaluation remains correct.

Let $\mathcal{E}=(\mathsf{KeyGen},\mathsf{Encrypt},\mathsf{Decrypt},\mathsf{Evaluate})$ be a homomorphic encryption scheme and $\mathcal{C}_{\mathcal{E}}$ a class of circuits for which it is correct: for every key pair output by $\mathsf{KeyGen}(\lambda)$, every $C\in\mathcal{C}_{\mathcal{E}}$ and every tuple $\Psi$ of ciphertexts output by $\mathsf{Encrypt}(pk,\pi_i)$, if $\psi\leftarrow\mathsf{Evaluate}(pk,C,\Psi)$ then $\mathsf{Decrypt}(sk,\psi)=C(\pi_1,\dots,\pi_t)$, except with negligible probability over the coins of $\mathsf{Evaluate}$. $\mathcal{E}$ is *circuit private for $\mathcal{C}_{\mathcal{E}}$* if, in addition, for every such key pair, every $t$-input $C\in\mathcal{C}_{\mathcal{E}}$ and every fixed $\Psi=(\psi_1,\dots,\psi_t)$ in the image of $\mathsf{Encrypt}$ on $\pi_1,\dots,\pi_t$, the distributions

$$
\mathsf{Encrypt}(pk,C(\pi_1,\dots,\pi_t))\quad\text{and}\quad\mathsf{Evaluate}(pk,C,\Psi),
$$

over the coins of $\mathsf{Encrypt}$ and $\mathsf{Evaluate}$, are statistically indistinguishable in $\lambda$. The key pair and input ciphertexts are fixed, not random.

The motivating setting is two-party computation with an honest-but-curious key holder, where the evaluator hides its circuit behind a ciphertext the key holder decrypts. Interactive protocols such as Gazelle's (Appendix B) instead avoid handing such a ciphertext to the key holder; that is a protocol-level mechanism, not this property. Delphi reports that an implementation without circuit-private parameters can leak information about linear layers.

## Depends on

- [Homomorphic encryption scheme](../../public-key/homomorphic-encryption/scheme.md)
- [Statistical indistinguishability of distribution ensembles](../../security-games/computational-indistinguishability-of-ensembles/statistical-indistinguishability-of-ensembles.md)

## Proof depends on

None.

## Expansion

A definition. Realizations (Gentry's randomization, Chapter 20; noise flooding; [sanitization](ciphertext-sanitization.md)) are separate results.

## Sources

- Craig Gentry, "A Fully Homomorphic Encryption Scheme", PhD thesis, Stanford University (2009), Definitions 2.1.1 and 2.1.6 (printed pp. 28–30), [author copy](https://crypto.stanford.edu/craig/craig-thesis.pdf).
- Chiraag Juvekar, Vinod Vaikuntanathan, Anantha Chandrakasan, "GAZELLE: A Low Latency Framework for Secure Neural Network Inference", 27th USENIX Security Symposium (2018), [USENIX copy](https://www.usenix.org/conference/usenixsecurity18/presentation/juvekar); preprint arXiv:1801.05507v1. Appendix B.
- Pratyush Mishra, Ryan Lehmkuhl, Akshayaram Srinivasan, Wenting Zheng, Raluca Ada Popa, "Delphi: A Cryptographic Inference Service for Neural Networks", 29th USENIX Security Symposium (2020), Remark 6.1, [USENIX open-access copy](https://www.usenix.org/conference/usenixsecurity20/presentation/mishra).
