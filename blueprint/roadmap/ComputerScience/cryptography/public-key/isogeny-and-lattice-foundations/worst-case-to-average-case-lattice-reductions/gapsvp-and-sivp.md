# Approximate lattice problems GapSVP and SIVP

For a full-rank lattice $\Lambda\subseteq\mathbb{R}^{n}$ given by a basis, let $\lambda_1(\Lambda)$ be the length of a shortest nonzero vector and $\lambda_n(\Lambda)$ the smallest $r$ such that $\Lambda$ contains $n$ linearly independent vectors of length at most $r$. For an approximation factor $\gamma=\gamma(n)\ge 1$: $\mathrm{GapSVP}_\gamma$ is the promise problem of deciding, given $(\Lambda,d)$, whether $\lambda_1(\Lambda)\le d$ or $\lambda_1(\Lambda)>\gamma d$; $\mathrm{SIVP}_\gamma$ asks to output $n$ linearly independent lattice vectors of length at most $\gamma\lambda_n(\Lambda)$. Both are believed hard for polynomial $\gamma$, even for quantum algorithms, and are the worst-case problems underlying LWE.

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", JACM (2009); STOC (2005).
- Chris Peikert, "Public-Key Cryptosystems from the Worst-Case Shortest Vector Problem", STOC (2009).
