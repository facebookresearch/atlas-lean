# Critical two-point boundedness and a coupled nonuniqueness interval

Let $G$ be an infinite connected locally finite labelled bond graph with finitely many vertex orbits under incidence-preserving automorphisms. Assume its vertex expansion $\inf_{A\ne\varnothing}|\partial_V A|/|A|$ over finite sets is positive, where $\partial_V A$ comprises neighbors outside $A$. Under the independent retention law $P_p$, write $\tau_p(x,y)=P_p(x\leftrightarrow y)$. Put $p_c=\inf\{p:P_p(\text{some infinite cluster})>0\}$, $p_u=\inf\{p:P_p(\text{exactly one infinite cluster})=1\}$, and $p_2=\sup\{p:\tau_p\text{ is the matrix of a bounded complex operator on }\ell^2(V)\}$. Write $N(p)$ for the extended nonnegative infimum of norms of operators with this matrix (infinity when there is no such operator).

Then $\sup_{p<p_c}N(p)=N(p_c)<\infty$ and $p_c<p_2\le p_u$. Also there exist $p_c<p_1<p_2'<1$ such that almost surely over one draw of independent uniform $[0,1]$ labels on all bonds, the graphs of bonds with label $\le p$ have infinitely many distinct infinite clusters simultaneously for all $p\in[p_1,p_2']$. The interval endpoint $p_2'$ is not defined to be the operator threshold $p_2$.

**Conventions.** Use the labelled-bond law, the origin-free cluster events, the two-point matrix on complex $\ell^2$, and a common label coupling. An almost-sure event for each fixed $p$ alone does not yield the asserted simultaneous event.

## Depends on

- [Independent bonds with separate edge labels](labelled-independent-bond-law.md)

## Proof depends on

The subcritical norm control and critical operator extension, the strict operator-threshold gap, and a coupled uniqueness/nonuniqueness argument for a closed interval inside the nonuniqueness phase.

## Expansion

First establish measurable joint labels and uniqueness of the bounded operator with given columns. Separate boundedness and the from-below norm identity, the threshold comparisons, and the interval event. Preserve distinct bonds in the operator and cluster calculations.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BenjaminiSchramm.lean#L216-L221)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/214.md)
- [Accompanying manuscript: Nonuniqueness of percolation on nonamenable quasi-transitive graphs](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf)
