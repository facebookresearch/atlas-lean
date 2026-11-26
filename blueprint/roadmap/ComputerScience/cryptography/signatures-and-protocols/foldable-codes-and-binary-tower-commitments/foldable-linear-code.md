# Foldable linear codes

Let $c,k_0\ge 1$ and $\mathbb{F}$ a field. A family of linear codes $C_0\subseteq\mathbb{F}^{n_0}$, $C_1,\dots,C_d$ with generator matrices $G_i\in\mathbb{F}^{k_i\times n_i}$, $k_i=2^{i}k_0$, $n_i=c\,k_i$, is *foldable* if there are diagonal matrices $T_{i},T'_{i}\in\mathbb{F}^{n_{i}\times n_{i}}$ with $T_i-T'_i$ invertible such that

$$
G_{i+1}=\begin{pmatrix}G_i & G_i\\ G_iT_i & G_iT'_i\end{pmatrix}.
$$

Thus a message $(m_0,m_1)$ of length $k_{i+1}$ encodes to $(m_0G_i+m_1G_iT_i,\;m_0G_i+m_1G_iT'_i)$, and from any two coordinates $j$, $j+n_i$ of a codeword of $C_{i+1}$ one recovers the $j$-th coordinates of $m_0G_i$ and $m_1G_i$.

## Sources

- Hadas Zeilberger, Binyi Chen, Ben Fisch, "BaseFold: Efficient Field-Agnostic Polynomial Commitment Schemes from Foldable Codes", CRYPTO (2024), IACR ePrint 2023/1705.
