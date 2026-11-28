# Rerandomizable and explainable garbling schemes

A *projective rerandomizable garbling scheme* (RGS) for a function family $\mathcal{F}$ with inputs in $\{0,1\}^m$ and a leakage function $\phi$ is a tuple $(\mathrm{Gb}, \mathrm{Rerand}, \mathrm{En}, \mathrm{Ev})$ of probabilistic polynomial-time algorithms using a common randomness space $R$, where $\mathrm{Gb}(f; r) = (F, e)$ with garbling coins $r \in R$ and $\mathrm{Rerand}(F; r') = (F', \pi)$ with rerandomizing coins $r' \in R$ outputs a new garbled circuit and a family $\pi$ of label permutations acting on encodings, satisfying:
- *Correctness:* $\mathrm{Ev}(F, \mathrm{En}(e, x)) = f(x)$ and $\mathrm{Ev}(F', \mathrm{En}(\pi(e), x)) = f(x)$ with probability $1$, for $(F, e) \leftarrow \mathrm{Gb}(f)$ and $(F', \pi) \leftarrow \mathrm{Rerand}(F)$.
- *Privacy:* for all $f_0, f_1 \in \mathcal{F}$ with $\phi(f_0) = \phi(f_1)$ and inputs with $f_0(x_0) = f_1(x_1)$, the pairs $(F_b, \mathrm{En}(e_b, x_b))$ with $(F_b, e_b) \leftarrow \mathrm{Gb}(f_b)$ are computationally indistinguishable for $b = 0, 1$.
- *Rerand-privacy:* for every $f \in \mathcal{F}$ and $x$, the triple $(r, F_0, \mathrm{En}(\pi(e), x))$ with $r$ uniform in $R$, $(F, e) = \mathrm{Gb}(f; r)$ and $(F_0, \pi) \leftarrow \mathrm{Rerand}(F)$ is computationally indistinguishable from $(r, F_1, \mathrm{En}(e_1, x))$ with $r$ uniform in $R$ and an independent fresh $(F_1, e_1) \leftarrow \mathrm{Gb}(f)$.
- *Projective encoding:* $\mathrm{En}(e, x)$ gives one label per input bit, depending only on that bit, and $\pi$ acts label by label.

An RGS is *explainable* if there is a function $\mathrm{Explain} : R \times R \to R$ satisfying, for all $f$ and $x$: *explainable garbling privacy*, $(f, X, F, F', \mathrm{Explain}(r, r'))$ with uniform $r, r' \in R$, $(F, e) = \mathrm{Gb}(f; r)$, $X = \mathrm{En}(e, x)$ and $F' = \mathrm{Rerand}(F; r')$ is computationally indistinguishable from $(f, X, F, G, s)$ with uniform $r, s \in R$, $(F, e) = \mathrm{Gb}(f; r)$, $X = \mathrm{En}(e, x)$ and $G = \mathrm{Gb}(f; s)$; and *explainable rerandomizing privacy*, $(F^*, X, F, F', \mathrm{Explain}(r, r'))$ with $(F^*, e) \leftarrow \mathrm{Gb}(f)$, uniform $r, r' \in R$, $(F, \pi) = \mathrm{Rerand}(F^*; r)$, $X = \mathrm{En}(\pi(e), x)$ and $F' = \mathrm{Rerand}(F; r')$ is computationally indistinguishable from $(F^*, X, F, G, s)$ with $(F^*, e) \leftarrow \mathrm{Gb}(f)$, uniform $r, s \in R$, $(F, \pi) = \mathrm{Rerand}(F^*; r)$, $X = \mathrm{En}(\pi(e), x)$ and $G = \mathrm{Rerand}(F^*; s)$. The explanation is computed from the garbling and rerandomizing coins, not from the garbled circuit alone.

## Remarks

In Acharya, Hazay, Kolesnikov and Prabhakaran (CRYPTO 2024, proof of Lemma 2 for Construction 1), the concrete construction satisfies the randomness composition identity $\mathrm{Gb}(f; \mathrm{Explain}(r, r')) = (F', \pi(e))$ when $(F, e) = \mathrm{Gb}(f; r)$ and $(F', \pi) = \mathrm{Rerand}(F; r')$.

## Depends on

- [Side-information functions and privacy notions for garbling schemes](../garbling-scheme-security/garbling-privacy-notions.md)

## Sources

- Anasuya Acharya, Carmit Hazay, Vladimir Kolesnikov and Manoj Prabhakaran, "Malicious Security for SCALES: Outsourced Computation with Ephemeral Servers", Advances in Cryptology – CRYPTO 2024, 2024, Definitions 3 and 9 (and Lemma 2 for Construction 1).
