# QuickSilver checks for polynomial constraints of arbitrary degree

Let $P$ be a polynomial constraint of degree $d \ge 1$ on IT-MAC-authenticated witness values over a finite field $\mathbb{F}$. Substituting the verifier's keys $k_w = m_w + w\Delta$ into the homogenization $\tilde P(k) = \sum_{h=0}^{d} P_h(k)\,\Delta^{d-h}$, where $P_h$ is the homogeneous degree-$h$ part of $P$, gives a polynomial in $\Delta$ of degree $d$ whose leading coefficient is $P(w)$; the prover sends the $d$ lower-order coefficients (masked with $d - 1$ fresh VOLE correlations), and the verifier checks $\tilde P(k) = \sum_{j<d} c_j\Delta^j + \Delta^d \cdot (\text{public value})$. If $P(w) \ne 0$ the check passes with probability at most $d/|\mathbb{F}|$ over a uniform key, and at most $d/|C|$ over a key uniform in the image of an embedding of a smaller set $C \hookrightarrow \mathbb{F}$; the honest verifier's full view is perfectly simulatable.

## Proof sketch

A nonzero univariate polynomial of degree $d$ has at most $d$ roots; the masks make the transmitted coefficients uniform subject to the verification equation.

## Depends on

- [Vector oblivious linear evaluation and IT-MACs](vole-correlations-and-it-macs.md)

## Proof depends on

- [Soundness of the VOLE multiplication check](vole-multiplication-check.md)
- [Zero knowledge of masked VOLE multiplication checks](masked-multiplication-check-zero-knowledge.md)

## Sources

- Kang Yang, Pratik Sarkar, Chenkai Weng and Xiao Wang, "QuickSilver: Efficient and Affordable Zero-Knowledge Proofs for Circuits and Polynomials over Any Field", Proceedings of the 2021 ACM SIGSAC Conference on Computer and Communications Security (CCS 2021), 2021.
- Carsten Baum et al., "FAEST v3: Algorithm Specifications", FAEST Team, 2026.
