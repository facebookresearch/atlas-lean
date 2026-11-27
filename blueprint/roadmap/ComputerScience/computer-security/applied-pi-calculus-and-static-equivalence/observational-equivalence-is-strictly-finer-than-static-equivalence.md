# Observational equivalence is strictly finer than static equivalence

**Lemma.** On closed extended processes of the [applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md), [observational equivalence](observational-equivalence-in-the-applied-pi-calculus.md)
implies [static equivalence](frames-and-static-equivalence.md), $\approx\ \subsetneq\ \approx_s$, and the two coincide on frames. The inclusion is strict:
$\overline a\langle n\rangle \not\approx \overline b\langle n\rangle$, while both have the frame $0$ and are statically equivalent.

## Depends on

- [Observational equivalence in the applied pi calculus](observational-equivalence-in-the-applied-pi-calculus.md)
- [Frames and static equivalence](frames-and-static-equivalence.md)
- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)

## Proof depends on

- [Observational equivalence is labelled bisimilarity](observational-equivalence-is-labelled-bisimilarity.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 4.2, Lemma 4.2 (a corollary of Theorem 4.1, Corollary C.2) and Lemma 4.3 with its counterexample.
