# Matching pursuit

Matching pursuit (S. Mallat and Z. Zhang, *Matching pursuits with time-frequency dictionaries*, IEEE Trans. Signal Process. 41 (1993), 3397–3415) expands a vector $f$ of a Hilbert space over a redundant dictionary of unit vectors $(g_\gamma)_{\gamma \in \Gamma}$, for instance Gabor time-frequency atoms. At step $n$ it selects an atom $g_{\gamma_n}$ that almost maximizes the correlation with the current residue, $|\langle R^n f, g_{\gamma_n}\rangle| \ge \alpha \sup_\gamma |\langle R^n f, g_\gamma\rangle|$ with $0 < \alpha \le 1$, and subtracts the projection on it: $R^{n+1} f = R^n f - \langle R^n f, g_{\gamma_n}\rangle g_{\gamma_n}$. The decomposition is nonlinear, yet it [conserves energy](norm-sq-eq-sum-add-norm-sq-residue.md) exactly as an orthogonal expansion would, whatever atoms are chosen: $\|f\|^2 = \sum_{n<m} |\langle R^n f, g_{\gamma_n}\rangle|^2 + \|R^m f\|^2$. With the weak greedy choice the residues [converge](tendsto-residue-star-projection-orthogon.md) to the component of $f$ orthogonal to the dictionary, so a complete dictionary yields $f = \sum_n \langle R^n f, g_{\gamma_n}\rangle g_{\gamma_n}$.

In an orthonormal basis matching pursuit simply reorders the orthogonal expansion by decreasing coefficients, which yields the [best $M$-term approximations](../best-m-term-approximation/README.md) in that basis; orthogonal matching pursuit re-projects on all atoms selected so far.

- [Matching pursuit residue](residue.md)
- [The new residue is orthogonal to the selected atom](inner-residue-succ-eq-zero.md)
- [One step of matching pursuit conserves energy](norm-sq-residue-eq.md)
- [The residue energy is nonincreasing](norm-residue-succ-le.md)
- [Matching pursuit decomposition](eq-sum-add-residue.md)
- [Energy conservation of matching pursuit](norm-sq-eq-sum-add-norm-sq-residue.md)
- [Convergence of matching pursuit](tendsto-residue-star-projection-orthogon.md)

## Related topics

- [Sparse recovery by orthogonal matching pursuit](../sparse-recovery-by-orthogonal-matching-pursuit/README.md): the orthogonal variant, which projects the signal on the span of all atoms selected so far, so that it never selects an atom twice and, under Tropp's Exact Recovery Condition, recovers a sparse representation exactly.
- [Best M-term approximation](../best-m-term-approximation/README.md): the orthonormal-basis case, where keeping the $M$ largest coefficients is optimal.
