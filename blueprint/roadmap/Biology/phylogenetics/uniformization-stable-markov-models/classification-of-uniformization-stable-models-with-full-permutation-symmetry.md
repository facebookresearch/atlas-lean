# Classification of uniformization stable models with full permutation symmetry

**Setting.** $S_n$ acts on matrices by simultaneous row and column permutation, $\sigma\cdot X=K_\sigma^TXK_\sigma$. A linear Markov model $\mathcal L^+=\mathcal L\cap\mathcal L_n^+$, with $\mathcal L$ the minimal subspace, has *full $S_n$-symmetry* if $\mathcal L$ is an $S_n$-module. Let $L_{ij}$ be the elementary rate matrix ($1$ at $(i,j)$, $-1$ at $(i,i)$), $L_\sigma=K_\sigma-I_n$, $J=\frac1n\mathbf 1\mathbf 1^T-I_n$, and $R_i$ the rate matrix with ones on the off-diagonal entries of column $i$.

**Decomposition.** For $n>3$, as $S_n$-modules,

$$\mathcal L_n\cong\{n\}\oplus2\{n-1,1\}\oplus\{n-2,2\}\oplus\{n-2,1^2\}.$$

A non-zero $S_n$-submodule gives a non-trivial model iff it contains $\mathrm{span}(J)\cong\{n\}$.

**Theorem.** The nontrivial, linear, uniformization stable Markov models with full $S_n$ symmetry are exactly the intersections with $\mathcal L_n^+$ of the following subspaces. For $n>4$:
- constant input $\mathrm{CI}_n=\mathrm{span}(J)$ (dimension $1$; the $n$-state Jukes–Cantor model);
- equal input $\mathrm{EI}_n=\mathrm{span}(R_i:i\in[n])$ (dimension $n$);
- symmetric $\mathrm{Symm}_n=\mathrm{span}(L_{ij}+L_{ji})$ (dimension $\tfrac12n(n-1)$);
- $\mathrm{EI}_n+\mathrm{Symm}_n$ (dimension $\tfrac12(n+2)(n-1)$);
- doubly stochastic $\mathrm{DS}_n=\mathrm{span}(L_\sigma:\sigma\in S_n)$ (dimension $(n-1)^2$);
- general Markov $\mathrm{GM}_n=\mathcal L_n$ (dimension $n(n-1)$).

For $n=2$: $\mathrm{CI}_2$ and $\mathrm{GM}_2=\mathrm{EI}_2=\mathcal L_2$. For $n=3$, the $n>4$ list plus the cyclic group-based model $\mathrm{span}(L_\sigma:\sigma\in C_3)$ and its sum with $\mathrm{EI}_3$ (dimensions $2$ and $4$). For $n=4$, the $n>4$ list plus the Klein-group model K3ST, $\mathrm{span}(L_\sigma:\sigma\in V_4)$ (dimension $3$), and K3ST+F81, its sum with $\mathrm{EI}_4$ (dimension $6$).

## Depends on

- [Uniformization stability is equivalent to a Jordan algebra](uniformization-stability-is-equivalent-to-a-jordan-algebra.md)

## Expansion

By the equivalence theorem it suffices to classify $S_n$-submodules of $\mathcal L_n$ containing $\{n\}$ that are Jordan algebras. Using an $S_n$-invariant inner product (sum of squared off-diagonal entries), submodules decompose orthogonally. Explicit Jordan products of the generators, such as $R_i\odot R_j=-(R_i+R_j)$ and $C_i\odot C_j=C_i+C_j-n(L_{ij}+L_{ji})$ for the row analogues $C_i$, show which combinations close: $\mathrm{EI}_n$ and $\mathrm{DS}_n$ are matrix algebras, $\mathrm{Symm}_n$ is Jordan but not Lie, and the antisymmetric module $\{n-2,1^2\}$ is Lie but not Jordan. Lemmas then force $\mathrm{Symm}_n\subseteq\mathcal L$ whenever $\{n-2,2\}$ is present ($n>4$) and $\mathrm{DS}_n\subseteq\mathcal L$ whenever $\{n-2,1^2\}$ is present ($n>3$), leaving only the listed subspaces; small $n$ admit the extra cyclic and Klein-group modules.

## Sources

- L. Cooper, J. Sumner, "Uniformization stable Markov models and their Jordan algebraic structure", arXiv:2105.03558 (2021), <https://doi.org/10.48550/arXiv.2105.03558>. Section 4 (Definitions 4.1, 4.2; Theorem 4.4; Lemmas 4.5, 4.6, 4.11–4.14; Theorem 4.15).
