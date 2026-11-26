# Operator norm of random matrices

The operator norm $\|M\|$ (the largest singular value; for a symmetric matrix, the largest
eigenvalue in absolute value) of an $n \times n$ random matrix with independent, mean-zero entries
bounded by $1$ is $O(\sqrt{n})$ with overwhelming probability (an $\varepsilon$-net argument), and
it concentrates with $O(1)$ fluctuations (Talagrand's inequality). For Wigner matrices with
i.i.d. entries of mean $0$, variance $1$ and finite fourth moment, $\|M_n\| / \sqrt{n} \to 2$
almost surely (Bai and Yin for the upper bound, the semicircle law for the lower bound). These are the topics of §2.3 of
Tao's *Topics in Random Matrix Theory*.

- [Upper tail estimate for Wigner ensembles](wigner-op-norm-upper-tail.md)
- [Concentration of the operator norm](op-norm-concentration-median.md)
- [Strong Bai–Yin theorem, upper bound](wigner-op-norm-le-two-add.md)
- [Bai–Yin theorem](tendsto-wigner-op-norm-div-sqrt.md)

## Related topics

- [Wigner's semicircle law](../wigner-s-semicircle-law/README.md)
- [Talagrand's concentration inequality](../../concentration-inequalities/talagrand-s-concentration-inequality/README.md)
- [Weyl's eigenvalue inequalities](../../../Analysis/operator-theory/eigenvalue-inequalities/weyl-s-eigenvalue-inequalities/README.md)
