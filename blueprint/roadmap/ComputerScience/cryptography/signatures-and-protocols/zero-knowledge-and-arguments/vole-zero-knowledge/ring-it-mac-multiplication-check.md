# Multiplication checks for IT-MACs over $\mathbb{Z}_{N^\zeta}$

Over the ring $\mathbb{Z}_{N^\zeta}$ with $N = pq$ (plaintexts of Damgård–Jurik encryption), a multiplication $z = xy$ of IT-MAC-authenticated values with keys $k_w = w\Delta + m_w$ is checked using one extra authenticated random value $r$: the prover sends two masked coefficients $(c_1, c_0)$ and the verifier checks a quadratic equation in $\Delta$. (i) If $z = xy$ the honest coefficients pass under every key; (ii) under a uniform mask $(r, m_r)$ the verifier's view $(k_r, c_1, c_0)$ has exactly the distribution produced by a simulator from the verifier's key alone; (iii) if $z \ne xy$, the check passes for a uniform key with probability at most $2/p_{\min}$, where $p_{\min} = \min(p, q)$ is the smallest prime factor of $N$, by the root bound for polynomials over $\mathbb{Z}_{N^\zeta}$ with a coefficient not divisible by $p_{\min}$.

## Proof sketch

Substitute the key relations; the leading coefficient is $xy - z$. A nonzero polynomial of degree $2$ over $\mathbb{Z}_{N^\zeta}$ whose leading coefficient is a unit modulo some prime factor has at most $2 N^\zeta/p_{\min}$ roots.

## Depends on

- [Vector oblivious linear evaluation and IT-MACs](vole-correlations-and-it-macs.md)

## Proof depends on

- [Hiding of VOLE commitments and binding of IT-MAC openings](it-mac-hiding-and-binding.md)

## Sources

- Carmit Hazay and Yibin Yang, "Toward Malicious Constant-Rate 2PC via Arithmetic Garbling", Advances in Cryptology – EUROCRYPT 2024, Part V, 2024.
