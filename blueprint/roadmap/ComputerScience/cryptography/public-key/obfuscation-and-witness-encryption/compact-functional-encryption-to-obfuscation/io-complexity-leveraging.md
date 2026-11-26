# Complexity leveraging for exponentially many hybrids

Suppose a primitive is secure with advantage at most $2^{-\lambda^{c}}$ for all adversaries of size $2^{\lambda^{c}}$, for a constant $c\in(0,1]$. If a proof uses $H=2^{n}$ hybrids, each indistinguishable by a reduction to the primitive with security parameter $\lambda$, then setting $\lambda=(n+\kappa)^{1/c}$ for the target security parameter $\kappa$ makes the total advantage of any polynomial-size adversary at most $2^{n}\cdot 2^{-(n+\kappa)}=2^{-\kappa}$, while the scheme remains polynomial-time in $n$ and $\kappa$.

## Proof sketch

Sum the per-hybrid advantages by the triangle inequality; the reductions run in polynomial time, below the size bound $2^{\lambda^{c}}$. The chosen $\lambda$ is polynomial in $n+\kappa$ since $c$ is a constant.

## Proof depends on

- [Single-key weakly compact public-key functional encryption](weakly-compact-fe.md)

## Sources

- Prabhanjan Ananth, Abhishek Jain, "Indistinguishability Obfuscation from Compact Functional Encryption", CRYPTO (2015), IACR ePrint 2015/173.
- Nir Bitansky, Vinod Vaikuntanathan, "Indistinguishability Obfuscation from Functional Encryption", FOCS (2015), IACR ePrint 2015/163.
