# Second-moment bound for block counts of coalescents with dust

**Setting.** Let $\Delta=\{u=(u_1\ge u_2\ge\dots\ge0):|u|=\sum_iu_i\le1\}$ be the ranked simplex parametrizing the paintbox of a merger event in an exchangeable coalescent with simultaneous multiple collisions ($\Xi$-coalescent): $u_i$ are the frequencies of the merging families and $u_0=1-|u|$ is the *dust*, the mass of blocks that stay singletons. When $n$ blocks are present and an event with paintbox $u$ occurs, assign each block independently to box $i\ge1$ with probability $u_i$ or to the dust with probability $u_0$; with $(X_0,X_1,\dots)$ the resulting box counts, the number of blocks after the event is

$$Y(n,u)=X_0+\sum_{i\ge1}\mathbf 1_{\{X_i>0\}}.$$

Let $\widetilde Y(n,u)=Y(n,u)/n-(1-|u|)$ and $p_n(u)=\mathbb E\widetilde Y(n,u)-\mathbb E[\widetilde Y(n,u)^2]$.

**Theorem (Möhle's Problem 6.3).** For every integer $n\ge1$ and every $u\in\Delta$, $p_n(u)\ge0$; that is,

$$\mathbb E\big[\widetilde Y(n,u)^2\big]\le\mathbb E\big[\widetilde Y(n,u)\big].$$

## Depends on

- [Block-count drift of a Λ-coalescent](block-drift.md)

## Expansion

The quantity $\widetilde Y(n,u)$ is the proportion of post-event blocks in excess of the dust's share, so $p_n\ge0$ bounds the second moment of the rescaled block count by its first moment uniformly over all paintboxes; Möhle posed it in the study of the block-counting process of exchangeable coalescents with dust. Expanding $\mathbb E\widetilde Y$ and $\mathbb E\widetilde Y^2$ through $\mathbb P(X_i=0)=(1-u_i)^n$ and $\mathbb P(X_i=X_{i'}=0)=(1-u_i-u_{i'})^n$, the collision terms are rewritten with the exact identities

$$(1-x)^n+(1-y)^n-1-(1-x-y)^n=-n(n-1)\int_0^x\!\!\int_0^y(1-r-t)^{n-2}\,dr\,dt,\qquad 1-(1-x)^n=n\int_0^x(1-t)^{n-1}dt,$$

which turn $p_n(u)$ into a sum over ordered pairs of families of integrals of a kernel whose sign can be certified on the finite simplex, giving nonnegativity for every $u$ and $n$.

## Sources

- D. S. P. Salazar, "Bernstein Functions at Work: Coalescents, Copulas, and Subordination", arXiv:2607.04467 (2026), Section 4.1 (Möhle's Problem 6.3 for coalescents with dust: binomial collision kernel lemma and Theorem 4.2), <https://doi.org/10.48550/arXiv.2607.04467>.
