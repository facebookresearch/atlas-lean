# Arc-number central limit theorem for canonical RNA secondary structures

**Setting.** An RNA secondary structure on $n$ nucleotides is a diagram on $\{1,\dots,n\}$ whose arcs (base pairs) $(i,j)$, $i<j$, are pairwise non-crossing and share no endpoints. It has *minimum arc-length* $\lambda$ if $j-i\ge\lambda$ for every arc, and is *$r$-canonical* if every stack (maximal run of nested parallel arcs $(i,j),(i+1,j-1),\dots$) has length at least $r$. Let $s^{[r]}_\lambda(n,l)$ count such structures with $l$ arcs and $\mathbf S^{[r]}_\lambda(x,y)=\sum_{n,l}s^{[r]}_\lambda(n,l)x^ny^l$.

**Theorem.**

*(1)* *(Functional equation.)* With $\mathbf A^{[r]}(x,y)=1-x^2y+(x^2y)^r$ and $\mathbf B^{[r]}_\lambda(x,y)=(1-x)\mathbf A^{[r]}(x,y)+(x^2y)^r\sum_{i=0}^{\lambda-2}x^i$,

$$(x^2y)^r\,\mathbf S^{[r]}_\lambda(x,y)^2-\mathbf B^{[r]}_\lambda(x,y)\,\mathbf S^{[r]}_\lambda(x,y)+\mathbf A^{[r]}(x,y)=0,$$

so that $\mathbf S^{[r]}_\lambda=\dfrac{\mathbf A^{[r]}}{\mathbf B^{[r]}_\lambda}\,\mathbf C\!\Big(\dfrac{(x^2y)^r\mathbf A^{[r]}}{(\mathbf B^{[r]}_\lambda)^2}\Big)$ with $\mathbf C(z)=\frac{1-\sqrt{1-4z}}{2z}$ the Catalan generating function.

*(2)* *(Central limit theorem.)* For $1\le\lambda\le4$ and $1\le r\le3$, let $Y^{[r]}_{\lambda,n}$ be the number of arcs of a uniformly random $r$-canonical structure of length $n$ with minimum arc-length $\lambda$. There are constants $\mu^{[r]}_\lambda,\sigma^{[r]}_\lambda>0$, given by $\mu=-\theta'(0)/\theta(0)$ and $\sigma^2=(\theta'(0)/\theta(0))^2-\theta''(0)/\theta(0)$ where $\theta(s)=\rho^{[r]}_\lambda(e^s)$ and $\rho^{[r]}_\lambda(y)$ is the dominant singularity of $x\mapsto\mathbf S^{[r]}_\lambda(x,y)$, such that

$$\frac{Y^{[r]}_{\lambda,n}-\mu^{[r]}_\lambda n}{\sqrt{n}\,\sigma^{[r]}_\lambda}\xrightarrow{d}\mathcal N(0,1)$$

with speed of convergence $O(n^{-1/2})$.

Numerically, $\mu^{[1]}_2=0.2764$, $\mu^{[2]}_4=0.2865$, and for the biophysically realistic case $\lambda=4$, $r=3$ (hairpins with at least three unpaired bases, stacks of length at least three) $\mu^{[3]}_4=0.3113$ arcs per nucleotide with $(\sigma^{[3]}_4)^2=0.0793$.

## Expansion

The functional equation comes from the usual decomposition of a secondary structure by its first nucleotide (unpaired, or paired to some later position), with stacks of length at least $r$ inserted as blocks of $r$ parallel arcs and the hairpin restriction removing short arcs. Solving the quadratic gives an algebraic generating function with a square-root singularity $\rho^{[r]}_\lambda(y)$ that moves analytically with $y$ near $1$. A quasi-power argument (Bender's theorem with the Flajolet–Sedgewick transfer theorems) then yields the Gaussian limit for the number of arcs with mean and variance read off from $\rho$. The arc distribution of uniformly random structures with $\lambda=4$, $r=3$ closely matches that of minimum free energy structures folded from random sequences, which is why the combinatorial model is a useful proxy.

## Depends on

- [RNA secondary structure](../../nussinov-algorithm-for-rna-secondary-structure/is-structure.md)
- [Waterman's recursion](../../mccaskill-partition-function-for-rna-folding/waterman-number.md)

## Sources

- C. L. Barrett, T. J. X. Li, C. M. Reidys, "RNA secondary structures having a compatible sequence of certain nucleotide ratios", arXiv:1603.03653 (2016), Section "RNA secondary structures": Theorem 6, Theorem 7 (coefficient asymptotics for $1\le\lambda\le4$, $1\le r\le3$), Theorem 8 and its table of $\mu^{[r]}_\lambda$ and $(\sigma^{[r]}_\lambda)^2$; Section "Singularity analysis", Theorem 5, <https://doi.org/10.48550/arXiv.1603.03653>.
