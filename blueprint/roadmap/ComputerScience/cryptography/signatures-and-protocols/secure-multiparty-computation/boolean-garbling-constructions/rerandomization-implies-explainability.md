# Rerandomization privacy implies explainable garbling

The rerandomizable garbled-circuit scheme of Acharya, Hazay, Kolesnikov and Prabhakaran (CRYPTO 2024, Construction 1, built from a sharable strong key- and message-homomorphic encryption scheme, Definition 17) is an explainable rerandomizable garbling scheme (Definition 9): there exists an explicit function $\mathrm{Explain}$ composing the garbling randomness $r$ and the rerandomization randomness $r'$ into randomness $r^* = \mathrm{Explain}(r, r')$ such that, for $(F, e) = \mathrm{Gb}(f; r)$ and $(F', \pi) = \mathrm{Rerand}(F; r')$, the rerandomized circuit satisfies $F' = \mathrm{Gb}(f; r^*)$, and the scheme satisfies both explainable garbling privacy and explainable rerandomizing privacy (Acharya, Hazay, Kolesnikov and Prabhakaran, CRYPTO 2024, Lemma 2 and Appendix A.3). This lets parties in maliciously secure protocols prove that rerandomized garbled material was honestly generated.

## Proof sketch

In Construction 1 (Appendix A.3, proof of Lemma 2), $\mathrm{Explain}(r, r')$ applies each wire's key-transformation function $\sigma_w$ to the garbling wire labels, applies each gate's share-randomizing function $h_i$ to the sharing randomness, and adds the encryption and rerandomization randomnesses, giving $F' = \mathrm{Gb}(f; r^*)$; hybrid arguments using the underlying KMHE security and rerandomization privacy then establish explainable garbling privacy and explainable rerandomizing privacy. More generally (as proved in the ePrint full version, not stated generically in the CRYPTO 2024 proceedings), for any projective rerandomizable garbling scheme equipped with a function $\mathrm{Explain}$ satisfying garbling randomness composition ($\mathrm{Gb}(f; \mathrm{Explain}(r, r')) = (F', \pi(e))$) and rerandomizing randomness composition ($\mathrm{Rerand}(F^*; \mathrm{Explain}(r, r')) = (F', \pi \circ \pi')$), any distinguisher against explainable garbling privacy or explainable rerandomizing privacy reduces directly to rerandomization privacy with the same advantage.

## Depends on

- [Rerandomizable and explainable garbling schemes](rerandomizable-garbling.md)

## Sources

- Anasuya Acharya, Carmit Hazay, Vladimir Kolesnikov and Manoj Prabhakaran, "Malicious Security for SCALES: Outsourced Computation with Ephemeral Servers", Advances in Cryptology – CRYPTO 2024, LNCS 14929, 2024, Definition 9, Construction 1, Lemma 2, and Appendix A.3 (proof of Lemma 2).
