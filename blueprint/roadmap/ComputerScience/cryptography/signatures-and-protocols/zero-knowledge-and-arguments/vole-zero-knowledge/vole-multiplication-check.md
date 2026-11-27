# Soundness of the VOLE multiplication check

For authenticated values $x, y, z$ with verifier keys $k_x, k_y, k_z$ and global key $\Delta$, the verifier accepts a claimed multiplication $z = xy$ with prover coefficients $(a, b)$ if $k_x k_y - k_z \Delta = a\,\Delta + b$. The honest coefficients $a = m_x y + m_y x - m_z$, $b = m_x m_y$ are always accepted. If $z \ne xy$, then for arbitrary (fixed or randomized, chosen before $\Delta$ is sampled) coefficients the check passes for at most two keys, hence with probability at most $2/|\mathbb{F}|$. For a batch of $t$ multiplication claims weighted by a public random vector (or by powers $\chi^{i+1}$ of one public scalar, as in QuickSilver) chosen after the values and masks are fixed, if some claim is false the batched check passes with probability at most $2/|\mathbb{F}|$ plus the probability $1/|\mathbb{F}|$ (respectively $t/|\mathbb{F}|$) that the weighted residual vanishes.

## Proof sketch

Substituting $k_w = m_w + w\Delta$, the check is a polynomial identity of degree $2$ in $\Delta$ whose leading coefficient is $xy - z$; a nonzero quadratic has at most two roots. For batching, the leading coefficient is the weighted residual, nonzero except with the stated probability.

## Depends on

- [Vector oblivious linear evaluation and IT-MACs](vole-correlations-and-it-macs.md)

## Proof depends on

- [Hiding of VOLE commitments and binding of IT-MAC openings](it-mac-hiding-and-binding.md)

## Sources

- Kang Yang, Pratik Sarkar, Chenkai Weng and Xiao Wang, "QuickSilver: Efficient and Affordable Zero-Knowledge Proofs for Circuits and Polynomials over Any Field", Proceedings of the 2021 ACM SIGSAC Conference on Computer and Communications Security (CCS 2021), 2021.
- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
