# Reduced LWE pairs from lattice reduction of the sample matrix

Lattice reduction applied to a $q$-ary embedding of $m$ LWE samples yields an integer matrix $R$ with $RA$ short modulo $q$. The transformed pairs $(RA,Rb)$ satisfy the LWE relation with the same secret and error $Re$ modulo $q$, where $e$ is the original integer error; they are in general not samples of the original LWE distribution.

Let $A\in\mathbb{Z}_q^{m\times n}$, $s\in\mathbb{Z}_q^n$, and let $e\in\mathbb{Z}^m$ be the original integer errors, so that $b\equiv As+e\pmod q$ (in the attacks, $m\le n$ samples chosen without replacement from a pool of about $4n$ collected samples). For an integer penalty parameter $\omega\ge1$ (the papers use $\omega=15$ or $\omega=10$), lattice reduction (LLL, BKZ, BKZ 2.0 or flatter) is applied to the rows of the $(m+n)\times(m+n)$ integer matrix

$$
\Lambda=\begin{pmatrix}0 & qI_n\\ \omega I_m & A\end{pmatrix}
$$

(entries of $A$ as integer representatives). The output rows have the form $[\,\omega R\ \ \ RA+qC\,]$ for integer matrices $R,C$; the attack extracts $R$. The **reduced pairs** are the rows of

$$
(RA \bmod q,\ Rb \bmod q).
$$

**Exact identity.** For every integer matrix $R$ with $m$ columns,

$$
Rb-(RA)s\equiv Re \pmod q ,
$$

so the reduced pairs obey the LWE relation with the same secret and error $Re$ modulo $q$. The identity holds for any choice of integer representatives of $A$, $b$, $s$. The reduced rows are typically neither uniform nor independent and the entries of $Re$ are correlated, so the reduced pairs are in general not samples of an LWE distribution ($R$ equal to the identity on $m$ rows is a trivial exception).

**Conditional error moment.** Suppose the entries of $e$ are independent with mean $0$ and variance $\sigma^2$, and $e$ is independent of the pair ($A$, randomness of the reduction), so that $R$ is a function of quantities independent of $e$. Then, conditional on $R$, the integer $(Re)_i=\sum_jR_{ij}e_j$ has mean $0$ and variance $\sigma^2\|r_i\|^2$, where $r_i$ is the $i$-th row of $R$. This concerns the unwrapped integer vector $Re$, not its representatives modulo $q$.

**Reduction factor (Salsa Fresca).** Reduction is measured by $\rho=\sigma(RA)/\sigma(A)$, where $\sigma(\cdot)$ is the mean over rows of the standard deviation of a row's entries (centred representatives), defined when $\sigma(A)>0$. The Cool and the Cruel paper uses a different $\rho$: the standard deviation of all entries of the reduced matrix divided by $q/\sqrt{12}$.

## Expansion

The identity is linearity over $\mathbb{Z}$ followed by reduction modulo $q$; replacing $RA$ by $RA+qC$ does not change residues. The conditional variance is that of a fixed linear combination of independent centred variables. Source-specific choices: SALSA PICANTE reduces $\begin{pmatrix}\omega I_n & A\\ 0 & qI_n\end{pmatrix}$ for square $A$ with $\omega=15$ and describes $\omega$ as trading reduction of $A$ against error growth; SALSA VERDE reorders the rows as displayed, uses $\omega=10$ and interleaves BKZ 2.0 with a polishing step; Salsa Fresca allows $m\le n$ and adds flatter. These are the papers' choices and observations, not general monotonicity statements. Taking $n$ of the $4n$ original samples copies them, so each chosen batch consists of genuine LWE samples before reduction.

## Depends on

- [LWE with a prescribed secret distribution](../small-and-sparse-secret-lwe/lwe-with-a-secret-distribution.md)
- [The block Korkine–Zolotarev (BKZ) reduction algorithm](../../../../algebraic-and-numerical-algorithms/lattice-basis-reduction/bkz-algorithm.md)
- [The Lenstra–Lenstra–Lovász algorithm](../../../../algebraic-and-numerical-algorithms/lattice-basis-reduction/the-lenstralenstralovasz-algorithm.md)

## Proof depends on

None.

## Sources

- Cathy Yuanchen Li, Jana Sotáková, Emily Wenger, Mohamed Malhou, Evrard Garcelon, François Charton, Kristin Lauter, "SALSA PICANTE: a machine learning attack on LWE with binary secrets", ACM CCS 2023, https://doi.org/10.1145/3576915.3623076; numbers from arXiv:2303.04178v3, Section 4.1.
- Cathy Yuanchen Li, Emily Wenger, Zeyuan Allen-Zhu, François Charton, Kristin Lauter, "SALSA VERDE: a machine learning attack on Learning With Errors with sparse small secrets", Advances in Neural Information Processing Systems 36 (NeurIPS 2023); numbers from arXiv:2306.11641v2, Section 2 (data preprocessing).
- Samuel Stevens, Emily Wenger, Cathy Li, Niklas Nolte, Eshika Saxena, François Charton, Kristin Lauter, "Salsa Fresca: Angular Embeddings and Pre-Training for ML Attacks on Learning With Errors", Transactions on Machine Learning Research (2025); numbers from arXiv:2402.01082v1, Section 2.1 and Table 2.
- Niklas Nolte, Mohamed Malhou, Emily Wenger, Samuel Stevens, Cathy Li, François Charton, Kristin Lauter, "The Cool and the Cruel: Separating Hard Parts of LWE Secrets", AFRICACRYPT 2024, Lecture Notes in Computer Science; numbers from arXiv:2403.10328v2, Section 3, Equation (3), and Section 4, Equation (5).
