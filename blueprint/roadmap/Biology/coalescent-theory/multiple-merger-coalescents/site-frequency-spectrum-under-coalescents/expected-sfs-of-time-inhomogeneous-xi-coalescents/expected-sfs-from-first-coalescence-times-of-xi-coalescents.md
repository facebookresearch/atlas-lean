# Expected SFS of a Ξ-coalescent from first-coalescence times

**Setting.** Let $\Xi$ be a finite measure on the infinite simplex, and consider the time-inhomogeneous $\Xi$-coalescent whose merger rates at time $t$ are those of $\Xi(d\mathbf{x})/\zeta(t)$, where $\zeta > 0$ is the relative population size (for $\Xi = \delta_0$ this is Kingman's coalescent with variable size). Let $\mathbf{Q} \in \mathbb{R}^{n\times n}$ be the lower-triangular rate matrix of the block-counting process of the time-homogeneous coalescent ($\zeta \equiv 1$), $\lambda_i = -(\mathbf{Q})_{ii}$, and let

$$c_{k,k} = \int_0^\infty \exp\!\Big((\mathbf{Q})_{kk}\int_0^t \frac{ds}{\zeta(s)}\Big)\,dt$$

be the expected time to the first coalescence among $k$ lineages. Write $\mathbf{c}_n = (c_{2,2},\dots,c_{n,n})^T$, $\mathbf{a}_n = (\mathbb{E}T^{(2)}_{\mathrm{MRCA}},\dots,\mathbb{E}T^{(n)}_{\mathrm{MRCA}})^T$, and $\boldsymbol{\tau}_n = (\tau_{n,1},\dots,\tau_{n,n-1})^T$ for the expected site frequency spectrum ($\tau_{n,i}$ is the expected number of segregating sites with $i$ derived copies in a sample of $n$) under the infinite-sites model with scaled mutation rate $\theta/2$.

**Theorem.** If $c_{k,k} < \infty$ for $2 \le k \le n$, then

$$\boldsymbol{\tau}_n = \frac{\theta}{2}\,\mathbf{A}\,\mathbf{a}_n, \qquad \mathbf{a}_n = \mathbf{L}\,\mathbf{c}_n,$$

where $\mathbf{A}$ is a universal matrix (independent of $\Xi$ and $\zeta$) and $\mathbf{L}$ depends on $\Xi$ but not on $\zeta$. Explicitly:

1. *(Anti-singletons.)* With $\boldsymbol{\gamma}_n = (\tau_{2,1},\tau_{3,2},\dots,\tau_{n,n-1})^T$, $\boldsymbol{\tau}_n = \mathbf{B}\boldsymbol{\gamma}_n$ where, for $i \le j$,

$$(\mathbf{B})_{ij} = (-1)^{i-j}\,\frac{1}{j+1}\binom{n-i-1}{j-i}\binom{n}{i},$$

and $(\mathbf{B})_{ij} = 0$ for $i > j$.

2. *(TMRCA increments.)* $\tau_{2,1} = \theta\,\mathbb{E}T^{(2)}_{\mathrm{MRCA}}$ and $\tau_{k+1,k} = \frac{\theta}{2}(k+1)\big(\mathbb{E}T^{(k+1)}_{\mathrm{MRCA}} - \mathbb{E}T^{(k)}_{\mathrm{MRCA}}\big)$ for $k \ge 2$, i.e. $\boldsymbol{\gamma}_n = \frac{\theta}{2}\mathbf{C}\mathbf{a}_n$ with $\mathbf{C}$ bidiagonal; thus $\mathbf{A} = \mathbf{B}\mathbf{C}$.

3. *(Spectral step.)* If the $\lambda_i$ are distinct, $\mathbf{Q} = \mathbf{U}\mathbf{E}\mathbf{U}^{-1}$ with $\mathbf{E} = \mathrm{diag}((\mathbf{Q})_{ii})$, $(\mathbf{U})_{ii} = 1$ and $(\mathbf{U})_{ij} = (\lambda_i - \lambda_j)^{-1}\sum_{k=j}^{i-1}(\mathbf{Q})_{ik}(\mathbf{U})_{kj}$ for $i > j$; then $\mathbf{L} = -(\mathbf{U}\mathbf{D})_{2:n,2:n}$ with $\mathbf{D} = \mathrm{diag}$ of the first column of $\mathbf{U}^{-1}$.

Consequently the expected SFS depends on the size history $\zeta$ only through the $n-1$ numbers $\mathbf{c}_n$, it is computable in $O(n^3)$ time, and in $O(n^2)$ time when $\zeta$ is constant. Moreover $\boldsymbol{\tau}_n$ and $\mathbf{a}_n$ determine each other (the maps are bijective) for every $\Lambda$- and $\Xi$-coalescent.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../../../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

Both universal identities come from exchangeability under subsampling. Removing a uniform individual from a sample of size $k$ gives $\tau_{k-1,l} = \frac{l+1}{k}\tau_{k,l+1} + \frac{k-l}{k}\tau_{k,l}$, which inverts level by level into the formula for $\mathbf{B}$. The TMRCA of a subsample of size $k$ differs from that of the full sample of $k+1$ only if the removed individual is the lone lineage left after all others have coalesced, an event weighted by $1/(k+1)$ whose expected duration times $\theta/2$ is the anti-singleton entry. Finally $\mathbb{P}(T^{(k)}_{\mathrm{MRCA}} > t) = \sum_{l\ge2}[e^{\mathbf{Q}\int_0^t \zeta^{-1}}]_{kl}$, and the spectral decomposition splits this into exponentials in $(\mathbf{Q})_{ll}\int_0^t\zeta^{-1}$, whose integrals are exactly the $c_{l,l}$.

## Sources

- Jeffrey P. Spence, John A. Kamm and Yun S. Song, "The Site Frequency Spectrum for General Coalescents", *Genetics* 202(4) (2016), 1549–1561. <https://doi.org/10.1534/genetics.115.184101>
- Preprint version (the locators in this item follow its numbering): Jeffrey P. Spence, John A. Kamm and Yun S. Song, "The site frequency spectrum for general coalescents", Genetics 202 (2016); arXiv:1510.05631, Section 2 (main theorem, corollary for constant size, and the anti-singleton, TMRCA, spectral-decomposition and first-coalescence lemmas) and Section 4 (bijection lemma), <https://doi.org/10.48550/arXiv.1510.05631>.
