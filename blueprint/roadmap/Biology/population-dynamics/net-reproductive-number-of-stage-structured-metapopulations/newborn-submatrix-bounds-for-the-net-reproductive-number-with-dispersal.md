# Newborn submatrix bounds for the net reproductive number with dispersal

**Model.** A population with $m \ge 2$ stages lives on $n$ patches. In patch $i$, stage-$k$ individuals have fecundity $f^{(i)}_k \ge 0$ (newborns enter stage $1$), stay in stage $k$ with probability $s^{(i)}_{k,k}$ and advance with probability $s^{(i)}_{k+1,k}$, where $s^{(i)}_{k,k} + s^{(i)}_{k+1,k} < 1$. The local Usher matrix is $A^{(i)} = F^{(i)} + S^{(i)}$, with $F^{(i)}$ carrying the fecundities in its first row and $S^{(i)}$ the lower-bidiagonal survival matrix. After local demography, a stage-$k$ individual moves from patch $j$ to patch $i$ with probability $d^{(i,j)}_k$, $\sum_i d^{(i,j)}_k = 1$. With block matrices $F = \bigoplus_i F^{(i)}$, $S = \bigoplus_i S^{(i)}$ and the dispersal matrix $D = (D^{(i,j)})$, $D^{(i,j)} = \mathrm{diag}(d^{(i,j)}_1, \dots, d^{(i,j)}_m)$, the population evolves by $x(t+1) = D(F + S)x(t)$. Define

$$ N = DF(I - DS)^{-1}, \qquad \mathcal R_0 = \rho(N), \qquad W = F(I - DS)^{-1}, \qquad \widehat{\mathcal R}_0 = \max_{x \in \mathcal X}\|Nx\|_1, $$

where $\mathcal X$ is the set of nonnegative newborn distributions (unit $\ell^1$ norm, supported on stage-1 coordinates), and the local numbers $\mathcal R_0^{(i)} = \rho\big(F^{(i)}(I - S^{(i)})^{-1}\big)$. For a matrix $X$ let $\bar X$ be the $n\times n$ *newborn submatrix* of entries in the stage-1 rows and columns.

**Theorem.**

1. $\bar N = \bar D\,\bar W$, $\rho(\bar N) = \rho(N) = \mathcal R_0$ and $\rho(\bar W) = \rho(W)$; moreover $\mathcal R_0 \le \|\bar N\|_1 \le \|N\|_1$ and $\widehat{\mathcal R}_0 = \|\bar W\|_1 \le \|W\|_1$. If newborns do not disperse ($d^{(i,i)}_1 = 1$ for all $i$), then $\bar D = I$ and $\mathcal R_0 = \rho(\bar W)$.
2. $\mathcal R_0 \le \widehat{\mathcal R}_0$, and there is $\xi \in \mathcal X$ with $\mathcal R_0 = \|N\xi\|_1$ and

$$ \min_j \sum_i \bar N_{ij} \le \mathcal R_0 \le \max_j \sum_i \bar N_{ij}; $$

   if $\bar N$ is irreducible, $\xi$ can be taken as the Perron vector of $\bar N$ placed on the newborn coordinates, so $\mathcal R_0$ is the expected lifetime reproductive output of a newborn with that spatial distribution.
3. *(Only newborns disperse.)* If $DS = S$, then $\bar W = \mathrm{diag}\big(\mathcal R_0^{(1)}, \dots, \mathcal R_0^{(n)}\big)$, $\bar N_{ij} = d^{(i,j)}_1\mathcal R_0^{(j)}$, $\widehat{\mathcal R}_0 = \max_i \mathcal R_0^{(i)}$, and

$$ \min_i \mathcal R_0^{(i)} \le \mathcal R_0 \le \max_i \mathcal R_0^{(i)}, $$

   with $\mathcal R_0$ strictly increasing in $\mathcal R_0^{(j)}$ whenever newborns from patch $j$ can reach some patch. In this case dispersal cannot amplify the net reproductive number beyond the best patch; amplification above every local value (so that a metapopulation persists although each isolated patch would go extinct) requires dispersal of non-newborn stages.

## Expansion

An individual alive in stage $k$ survives and disperses through $DS$ each step and reproduces through $DF$, so its expected lifetime offspring vector is $\sum_{t \ge 0}DF(DS)^t x = DF(I - DS)^{-1}x$; the series converges because $D$ is column stochastic and $\|S\|_1 < 1$. All offspring are newborns, so $N$ has nonzero rows only at stage-1 coordinates; projecting with the auxiliary matrices that embed and extract newborn coordinates shows that $N$ and $\bar N$ share their nonzero eigenvalues, which yields the reduction to the $n \times n$ matrix $\bar N$. The column-sum bounds are the standard bounds for the spectral radius of a nonnegative matrix. When only newborns disperse, $(I - DS)^{-1} = (I - S)^{-1}$ is block diagonal, so $\bar W$ is diagonal with the local reproductive numbers, and $\bar N = \bar D\,\mathrm{diag}(\mathcal R_0^{(j)})$ has column sums exactly $\mathcal R_0^{(j)}$. The graph-reduction method of de-Camino-Beck and Lewis computes $\mathcal R_0$ from $\bar N$ symbolically; in the round goby application a cubic $u^3 - au - b$ arises whose unique positive root lies on the same side of $1$ as $a + b$.

## Sources

- Matt S. Calder, Yingming Zhao, Xingfu Zou, "Amplification of the net reproductive number by dispersion for a matrix population model applicable to the invasive round goby fish", arXiv:1311.4822 (2013), Section 2 (model and next-generation definitions, Propositions 2.4, 2.8, 2.9, Theorem 2.11, Corollary 2.12, Theorem 2.13), Section 3 (Propositions 3.1 and 3.6, examples), Appendix (Propositions B.1–B.3). <https://doi.org/10.48550/arXiv.1311.4822>
