# Approximation ratio for sorting by transpositions

Improve the polynomial-time approximation guarantee for minimum block-transposition distance, or establish a matching approximation barrier. This is distinct from the transposition-diameter problem, which concerns worst-case distance; this one concerns finding short rearrangement sequences efficiently.

## What would settle it

Exhibit an algorithm A and a constant $\rho < 11/8$ with a polynomial running-time proof and $\mathrm{cost}(A(\pi)) \le \rho \cdot \mathrm{OPT}(\pi)$ for every permutation, or prove a precisely stated conditional hardness threshold. Correctness alone does not establish the approximation or time bounds.

## Status

The cited sources, in the versions cited, record the partial results below; they do not pose the question in this form, and this page does not certify its present status. This status evidence is older or incomplete; check later literature before relying on it.

Silva, Kowada, Rocco and Walter (preprint, §1) record the 1.375 = 11/8 approximation ratio and a result that the classical Bafna–Pevzner lower bound cannot support a ratio below 1.375. That barrier concerns one lower-bound technique, not every algorithm.

This page records the research target above and asserts no theorem or present-status certification.

## Sources

- Luiz A. G. Silva et al., *Twisted Bracelets for Sorting by Transpositions: the Transposition Diameter of S₁₆*, arXiv:2609.17493v3 (2026), §1. <https://arxiv.org/abs/2609.17493v3>
