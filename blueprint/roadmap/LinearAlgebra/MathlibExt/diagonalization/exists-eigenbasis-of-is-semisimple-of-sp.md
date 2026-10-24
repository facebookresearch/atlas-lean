---
article_id: af_266d4a6bce5c76a1a05900cf
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.DiagonalizationWanted.exists_eigenbasis_of_isSemisimple_of_splits
---

# Exists eigenbasis of is Semisimple of splits

A semisimple endomorphism whose characteristic polynomial splits admits a basis of
eigenvectors.

Proof: the minimal polynomial is squarefree and splits, so it is a product of distinct factors
`X - C μ`. The kernels lemma for these factors (induction from
`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`) shows the eigenspaces span `V`, and bases
of the eigenspaces are collected and reindexed. This is the diagonalizability criterion derived
from the kernels lemma in the French Wikipedia article *Lemme des noyaux*,
https://fr.wikipedia.org/wiki/Lemme_des_noyaux.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Diagonalization](../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms / diagonalization; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 1.3.12.
