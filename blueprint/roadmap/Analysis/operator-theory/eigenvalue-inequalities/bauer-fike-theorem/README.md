# Bauer–Fike theorem

Bauer and Fike (1960) localise the eigenvalues of a perturbed matrix: if $\mu$ is an eigenvalue of $A + E$ but not of $A$, then $1 \le \|(\mu - A)^{-1}E\| \le \|(\mu - A)^{-1}\|\,\|E\|$. For a diagonalizable $A = V \Lambda V^{-1}$ this gives $\min_i |\mu - \lambda_i| \le \|V\|\,\|V^{-1}\|\,\|E\|$ in the spectral norm, so the condition number of the eigenvector matrix measures the sensitivity of the eigenvalues; for normal matrices and operators it is $1$.

- [Resolvent norm bound for a normal operator](norm-ring-inverse-sub-smul-one-le.md)
- [Bauer–Fike theorem for normal operators](inf-dist-le-norm-of-mem-spectrum-add.md)
- [Attained form of the Bauer–Fike theorem for normal operators](exists-mem-spectrum-norm-sub-le.md)
- [Hausdorff distance between spectra of self-adjoint perturbations](hausdorff-dist-spectrum-le-of-is-self-ad.md)
- [Bauer–Fike theorem for diagonalizable matrices](exists-norm-sub-le-of-mem-spectrum-add.md)
- [Bauer–Fike exclusion theorem](one-le-norm-inverse-mul-of-mem-spectrum.md)
- [Bauer–Fike exclusion theorem, product form](one-le-norm-inverse-mul-norm-of-mem-spec.md)

## Related topics

- [Weyl's eigenvalue inequalities](../weyl-s-eigenvalue-inequalities/README.md): for Hermitian matrices each eigenvalue, in decreasing order, moves by at most $\|E\|$.
- [Perturbation theory for linear systems](../../../../LinearAlgebra/matrix-decompositions/perturbation-theory-for-linear-systems/README.md): the same invertibility-under-perturbation argument, applied to linear systems.
