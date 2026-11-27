# Rerandomization privacy implies explainable garbling

Let $(\mathrm{Gb}, \mathrm{Rerand}, \mathrm{En}, \mathrm{Ev})$ be a projective rerandomizable garbling scheme with a function $\mathrm{Explain}$ satisfying both randomness-composition properties: *garbling randomness composition*, for all $r \in R_{\mathrm{Gb}}$ and $r' \in R_{\mathrm{Rerand}}$, if $(F, e) = \mathrm{Gb}(f; r)$ and $(F', \pi) = \mathrm{Rerand}(F; r')$ then $\mathrm{Gb}(f; \mathrm{Explain}(r, r')) = (F', \pi(e))$; and *rerandomizing randomness composition*, for all $r, r' \in R_{\mathrm{Rerand}}$ and every $(F^*, e)$ in the support of $\mathrm{Gb}(f)$, if $(F, \pi) = \mathrm{Rerand}(F^*; r)$ and $(F', \pi') = \mathrm{Rerand}(F; r')$ then $\mathrm{Rerand}(F^*; \mathrm{Explain}(r, r')) = (F', \pi \circ \pi')$. Then: (i) by garbling randomness composition, every distinguisher against explainable garbling privacy yields an explicit adversary against rerandomization privacy with the same advantage; (ii) by rerandomizing randomness composition, every distinguisher against explainable rerandomizing privacy likewise yields an explicit adversary against rerandomization privacy with the same advantage. Hence rerandomization privacy together with randomness composition makes the scheme explainable, as needed for malicious-security compilers that let parties prove their garbled material was honestly generated.

## Proof sketch

Randomness composition makes the garblings of $f$ reachable from one another by rerandomization, so a prior garbling can be read as a rerandomization of a later one, with coins supplied by $\mathrm{Explain}$. The adversary receives the rerandomization-privacy challenge $(r, F, X)$, computes the garbling determined by $r$, and hands the distinguisher the explainability tuple built from it, so that a real (rerandomized) challenge gives the left-hand distribution of the explainability property and a fresh one the right-hand distribution.

## Depends on

- [Rerandomizable and explainable garbling schemes](rerandomizable-garbling.md)

## Sources

- Anasuya Acharya, Carmit Hazay, Vladimir Kolesnikov and Manoj Prabhakaran, "Malicious Security for SCALES: Outsourced Computation with Ephemeral Servers", Advances in Cryptology – CRYPTO 2024, 2024.
