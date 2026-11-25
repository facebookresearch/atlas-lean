# Von Neumann's trace inequality, sorted upper form

Let $A$ and $B$ be real symmetric $d \times d$ matrices (indexed by a finite set) with eigenvalues $\alpha^\downarrow_0 \ge \dots \ge \alpha^\downarrow_{d-1}$ and $\beta^\downarrow_0 \ge \dots \ge \beta^\downarrow_{d-1}$ in decreasing order. Then

$$\operatorname{tr}(AB) \le \sum_{k=0}^{d-1} \alpha^\downarrow_k \beta^\downarrow_k .$$

It follows from the pairing form (some permutation $\tau$ has $\operatorname{tr}(AB) \le \sum_k \alpha^\downarrow_k\beta^\downarrow_{\tau(k)}$) and the rearrangement inequality. The bound is attained at $B = A$, and for symmetric matrices it refines von Neumann's trace inequality $|\operatorname{tr}(AB)| \le \sum_k \sigma_k(A)\sigma_k(B)$, since $\sum_k \alpha^\downarrow_k\beta^\downarrow_k \le \sum_k \sigma_k(A)\sigma_k(B)$.

## Informally uses

- [A pairing of eigenvalues bounds the trace of a product from above](exists-perm-trace-mul-le-sum-mul-eigenva.md): the pairing form, before rearrangement.

## Sources

- C. M. Theobald, An inequality for the trace of the product of two symmetric matrices, Math. Proc. Cambridge Philos. Soc. 77 (1975), 265–267 (main inequality).
- J. von Neumann, Some matrix-inequalities and metrization of matric-space, Tomsk Univ. Rev. 1 (1937), 286–300 (the singular-value form).
