---
article_id: af_91f5946f64560ad0213efd41
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted.srg_nonprincipal_eigenvalue_quadratic
---

# Srg nonprincipal eigenvalue quadratic

Every non-principal eigenvalue of a connected non-complete strongly regular
graph satisfies the quadratic `x ^ 2 = (ℓ - μ) * x + (k - μ)`.

Proof: Apply `IsSRGWith.matrix_eq` to an eigenvector; regularity makes its
coordinate sum zero, and the complement identity then gives the quadratic.
This is the proof of Theorem 9.1.2, (ii) ⇒ (iii), in Brouwer and Haemers,
Section 9.1.3.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Nonprincipal eigenvalue quadratic](nonprincipal-eigenvalue-quadratic.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.StronglyRegular](../../../../../../../sources/v2/MathlibExt.md)
- A. E. Brouwer and W. H. Haemers, Spectra of Graphs, Springer 2012, Ch. 9, eigenvalues of strongly regular graphs; C. Godsil and G. Royle, Algebraic Graph Theory, GTM 207, Ch. 10 (eigenvalues of strongly regular graphs).
