# Exponential kernel approximate identity

For every function $f : \mathbb{R} \to \mathbb{R}$
in $L^2(\mathbb{R})$,

$$
\lim_{n\to\infty} n\int_{\mathbb{R}}\int_{\mathbb{R}} f(x)f(y)e^{-2n|x-y|}\,dy\,dx
= \int_{\mathbb{R}} f(x)^2\,dx,
$$

where $n$ runs through the natural numbers and the integrals are with respect to Lebesgue measure.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Classical measure theory), `benchmark/level2/ma_proofbench_l2_96.lean` at openbmb/ma-proofbench@31bab4c.
