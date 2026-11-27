# Hiding of VOLE commitments and binding of IT-MAC openings

Let $R$ be a finite commutative ring. (i) *Hiding:* for every witness $x \in R^n$, if the sender's VOLE vector $u$ is uniform, the correction $x - u$ is uniform, so any two witnesses induce identical correction distributions. (ii) *Binding over $\mathbb{Z}_{N^\zeta}$:* let $N = pq$ with primes $p < q$ and $\zeta \ge 1$, and let the global key $\Delta$ be uniform in $\mathbb{Z}_{N^\zeta}$; for fixed values $x$, masks and a forged opening $(x', m')$ with $x' \ne x$, the forged opening passes verification with probability at most $1/p$ (Hazay and Yang, EUROCRYPT 2024, Lemma 1; Lemma 3 of the full version).

## Proof sketch

A forgery passes when $(x' - x)\Delta = m - m'$. Over $\mathbb{Z}_{N^\zeta}$ the map $\Delta \mapsto (x'-x)\Delta$ is a group homomorphism whose image is a nontrivial subgroup, whose order divides $p^\zeta q^\zeta$ and so is at least $p$; hence each value has at most $N^\zeta/p$ preimages, and the uniform key hits one with probability at most $1/p$. Other rings, outside the statement, are handled in the same way. Over a finite field $\mathbb{F}$ the linear equation in $\Delta$ has exactly one solution when $x' \ne x$, so a forged opening passes with probability $1/|\mathbb{F}|$ under a uniform key. Over $\mathbb{Z}_n$ ($n \ge 2$) with $a = x' - x \not\equiv 0$, the congruence $a\Delta \equiv m - m' \pmod n$ has either no solution or exactly $\gcd(a, n)$ solutions, and $\gcd(a, n)$ is a proper divisor of $n$, hence at most $n/p_{\min}$ for the smallest prime factor $p_{\min}$ of $n$; a forged opening therefore passes with probability at most $1/p_{\min}$.

## Depends on

- [Vector oblivious linear evaluation and IT-MACs](vole-correlations-and-it-macs.md)

## Sources

- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
- Carmit Hazay and Yibin Yang, "Toward Malicious Constant-Rate 2PC via Arithmetic Garbling", Advances in Cryptology – EUROCRYPT 2024, Part V, 2024; full version Cryptology ePrint Archive, Paper 2024/283, Section 5.1 (perfect hiding of IT-MACs and the correction $x - r$ that consumes a random IT-MAC $[r]$) and EUROCRYPT 2024 Lemma 1 / full-version Lemma 3 (statistical binding for IT-MACs over $\mathbb{Z}_{N^\zeta}$: a different opening succeeds with probability at most $1/p$).
