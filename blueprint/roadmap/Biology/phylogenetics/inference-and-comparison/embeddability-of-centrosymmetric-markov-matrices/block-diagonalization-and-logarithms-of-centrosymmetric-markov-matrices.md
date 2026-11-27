# Block diagonalization and logarithms of centrosymmetric Markov matrices

**Setting.** Let $J_m$ be the $m\times m$ exchange matrix (ones on the anti-diagonal) and $I_m$ the identity. A real $n\times n$ matrix $A$ is *centrosymmetric* (CS) if $J_nAJ_n=A$, i.e. $a_{ij}=a_{n+1-i,n+1-j}$. CS Markov matrices generalize the strand-symmetric nucleotide model to genetic alphabets of any size $n$ in which letters come in complementary pairs (for even $n$; one self-complementary letter for odd $n$), as in synthetic expanded DNA alphabets. Define

$$S_n=\begin{pmatrix}I_{n/2}&J_{n/2}\\ J_{n/2}&-I_{n/2}\end{pmatrix}\ (n\text{ even}),\qquad S_n=\begin{pmatrix}I_{\lfloor n/2\rfloor}&0&J_{\lfloor n/2\rfloor}\\0&1&0\\ J_{\lfloor n/2\rfloor}&0&-I_{\lfloor n/2\rfloor}\end{pmatrix}\ (n\text{ odd}),$$

and the generalized Fourier transform $F_n(A)=S_n^{-1}AS_n$.

**Lemma (block diagonalization).** For every CS matrix $A$ of order $n\ge2$, $F_n(A)=\mathrm{diag}(A_1,A_2)$ with $A_1$ of size $\lceil n/2\rceil$; if $A$ is a Markov (respectively rate) matrix then so is $A_1$.

**Theorem.** Let $A$ be a real CS matrix.

1. $A$ has a CS logarithm if and only if both blocks $A_1$ and $A_2$ admit a (real) logarithm.
2. If $A$ is invertible, it has infinitely many CS logarithms; if its principal logarithm $\mathrm{Log}(A)$ is defined, then $\mathrm{Log}(A)$ is CS.
3. If $A$ is an invertible CS Markov matrix with Jordan decompositions $A_i=N_iD_iN_i^{-1}$, then $S_n\,\mathrm{diag}(N_1,N_2)\,\mathrm{diag}(D_1',D_2')\,\mathrm{diag}(N_1,N_2)^{-1}S_n^{-1}$, with $D_i'$ any logarithm of $D_i$, gives countably many (primary, CS) logarithms of $A$.
4. **(Necessary condition.)** If $A=(a_{ij})$ is an embeddable CS Markov matrix with a CS Markov generator, then

$$\sum_{j=1}^{n/2}\bigl(a_{jj}+a_{j,n-j+1}\bigr)>1\quad(n\text{ even}),\qquad \sum_{j=1}^{\lfloor n/2\rfloor}\bigl(a_{jj}+a_{j,n-j+1}\bigr)+a_{\lceil n/2\rceil,\lceil n/2\rceil}>1\quad(n\text{ odd}).$$

## Depends on

- [Embeddability criterion for strand-symmetric (4×4 centrosymmetric) Markov matrices](embeddability-criterion-for-strand-symmetric-markov-matrices.md)

## Expansion

Writing a CS matrix of even order in blocks $\begin{pmatrix}B_1&B_2\\ J B_2J&JB_1J\end{pmatrix}$ and using $S_n^{-1}=\tfrac12S_n$ (since $J^2=I$) gives $F_n(A)=\mathrm{diag}\bigl(B_1+B_2J,\ J(B_1-B_2J)J\bigr)$; symmetric vectors such as the all-ones vector are mapped into the first block, which is why $A_1$ inherits unit (or zero) row sums. Because $F_n$ is a similarity, $\exp$ commutes with it, so $Q=F_n^{-1}(\mathrm{diag}(Q_1,Q_2))$ is a CS logarithm whenever $Q_i$ are logarithms of $A_i$, and conversely. If $\mathrm{Log}(A)$ were not CS, $J_n\mathrm{Log}(A)J_n$ would be a second principal logarithm, contradicting uniqueness. For item 4, a CS generator $Q$ gives $A_1=\exp(Q_1)$ with $Q_1$ a rate matrix; one eigenvalue of $Q_1$ is $0$ and the others contribute positive exponentials, so $\mathrm{tr}A_1>1$, and $\mathrm{tr}A_1$ is the displayed sum.

## Sources

- Muhammad Ardiyansyah, Dimitra Kosta and Jordi Roca-Lacostena, "Embeddability of centrosymmetric matrices capturing the double-helix structure in natural and synthetic DNA", Journal of Mathematical Biology 86 (2023), 69, <https://doi.org/10.1007/s00285-023-01895-8>; numbering as in arXiv:2202.05889: Section 5: Proposition 5.4, Lemma 5.6, Theorem 5.8, Propositions 5.9–5.10, Theorem 5.11, Lemma 5.12.
