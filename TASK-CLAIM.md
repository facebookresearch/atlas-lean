# Task claim: partial fraction decomposition over the complex numbers

This temporary note opens the draft pull request that claims the ATLAS task
`af_1a9c04b49ac6ba64ccd0e9e8`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Algebra/polynomials/partial-fraction-decomposition/rat-func-partial-fractions-complex.md`
- Lean declaration: `MathlibExt.FieldTheory.ComplexPartialFractionsWanted.ratFunc_partial_fractions_complex`,
  the only declaration of `WantedExt/FieldTheory/ComplexPartialFractionsWanted.lean`
- Sources: Mathlib `docs/undergrad.yaml` (partial fraction decomposition in `ℂ(X)`); S. Lang,
  *Algebra*, rev. 3rd ed., Springer, 2002, Ch. IV, §5.

Statement to prove, with its name and statement unchanged: every $f \in \mathbb{C}(X)$ is
$q + \sum_{p \in S} \sum_{k < m_p} g_{p,k} / p^{k+1}$ for a polynomial $q$, a finite set $S$ of monic
polynomials of degree $1$, and polynomials $g_{p,k}$ of degree less than that of $p$.
