# Hiding of VOLE commitments and binding of IT-MAC openings

Let $R$ be a finite commutative ring. (i) *Hiding:* for every witness $x \in R^n$, if the sender's VOLE vector $u$ is uniform, the correction $x - u$ is uniform, so any two witnesses induce identical correction distributions. (ii) *Binding over a finite field $\mathbb{F}$:* for fixed values $x$, masks and a forged opening $(x', m')$ with $x' \ne x$, the forged opening passes verification for at most one global key $\Delta$, hence with probability at most $1/|\mathbb{F}|$ under a uniform key. (iii) *Binding over the finite ring $\mathbb{Z}_n$ ($n \ge 2$):* a forged opening $x' \ne x$ passes for a uniform key in $\mathbb{Z}_n$ with probability at most $1/p_{\min}$, where $p_{\min}$ is the smallest prime factor of $n$ (for $n = N^\zeta$ with $N = pq$, at most $1/\min(p, q)$); the number of keys accepting the forgery is at most $n/p_{\min}$.

## Proof sketch

A forgery passes when $(x' - x)\Delta = m - m'$; over a field this linear equation in $\Delta$ has at most one solution. Over $\mathbb{Z}_n$, the number of solutions is the size of the annihilator-coset of the nonzero difference, at most $n / p_{\min}$.

## Depends on

- [Vector oblivious linear evaluation and IT-MACs](vole-correlations-and-it-macs.md)

## Sources

- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
- Carmit Hazay and Yibin Yang, "Toward Malicious Constant-Rate 2PC via Arithmetic Garbling", Advances in Cryptology – EUROCRYPT 2024, Part V, 2024.
