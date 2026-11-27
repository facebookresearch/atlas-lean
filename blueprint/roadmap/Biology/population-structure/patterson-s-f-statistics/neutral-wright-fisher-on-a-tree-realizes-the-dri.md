# Neutral binomial drift on a tree realizes the drift model

On a finite rooted tree, take a root frequency $p_\rho\in[0,1]$.
For each edge $e$, choose integer $M_e\ge1$ and $t_e\ge0$.
Starting at the parent's frequency, perform $t_e$ neutral binomial
updates $p\mapsto\operatorname{Binomial}(M_e,p)/M_e$, using fresh
randomness for all updates. A zero-step edge leaves the frequency
unchanged. Initial frequencies need not be on the child edge's grid.
Let $\delta_e$ be the terminal minus initial frequency on the edge.
Then the increments have mean zero and pairwise zero cross moments, and

$$p_X=p_\rho+\sum_e w(X,e)\delta_e,\qquad
 \ell_e=\mathbb E\delta_e^2
 =\tfrac12\mathbb E[H_{\operatorname{start}(e)}]
 \left(1-(1-1/M_e)^{t_e}\right),$$

where $H_{\operatorname{start}(e)}=2p(1-p)$ and $w(X,e)$ is one on
the root-to-$X$ path and zero elsewhere. This realizes the canonical
[drift model](drift-model.md), including the root-only tree.
The edge increments are not required to be mutually independent.

## Depends on

- [Canonical drift model](drift-model.md)

## Proof depends on

- [Neutral lineage second moments](martingale-orthogonality-of-drift-increments-alo.md)
- [Single-root stochastic-graph realization](../admixture-graphs/admixture-graphs-as-graphical-models-soraggi-wiu.md)

## Expansion

Reveal edges in an order where each parent's frequency is known.
Fresh randomness and the binomial mean make the new increment conditionally
mean zero given all earlier revealed edges. Consequently distinct edge
increments are orthogonal. This covers both ancestor/descendant edges
and different branches, without claiming unconditional independence of
chains whose starting frequencies are shared. Conditional application of
the lineage formula gives the displayed length.

Dependence can be real: for two one-step edges with $M=2$ from root
frequency $1/2$, the second increment is zero if the first edge fixes
at zero or one, but its conditional variance is $1/8$ if the first edge
stays at $1/2$. In degenerate cases the increments can be independent,
so a universal non-independence claim would be false.
For a three-leaf tree with edges $\rho\to A$, $\rho\to U$,
$U\to B$, $U\to C$, orthogonality gives
$f_3(A;B,C)=\mathbb E[(p_B-p_A)(p_C-p_A)]
=\ell_{\rho A}+\ell_{\rho U}$. This checks the shared-path interpretation
with the reference population and signs specified.

## Sources

- S. Soraggi and C. Wiuf, *General theory for stochastic admixture graphs and F-statistics* (2019), <https://doi.org/10.1016/j.tpb.2018.12.002>, <https://arxiv.org/abs/1807.07593>, Example 2 and Theorem 3. Neutrality and absence of mutation are essential to the mean-preserving update used here.
