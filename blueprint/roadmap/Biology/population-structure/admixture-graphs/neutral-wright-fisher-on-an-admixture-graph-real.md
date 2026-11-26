# A pulse followed by binomial resampling realizes the drift model

In a finite single-root neutral admixture graph, represent a pulse from
parents $A,B$ with $0\le\alpha\le1$ by a noiseless node $X_0$ with
$q=\alpha p_A+(1-\alpha)p_B$. Its incoming edges have zero increments.
Use one outgoing edge $X_0\to X$ for $t\ge1$ neutral binomial updates
with integer $M\ge1$ gene copies, using fresh randomness after the
parental history. In particular the first count is
$\operatorname{Binomial}(M,q)$. Let $\eta=p_X-q$.
Combining such pulses with the neutral tree-edge construction gives

$$p_X=p_\rho+\sum_e w(X,e)\delta_e,\qquad
 \mathbb E\eta^2=\mathbb E[q(1-q)]\left(1-(1-1/M)^t\right).$$

All edge increments have mean zero and distinct increments are orthogonal;
thus the graph is a [drift model](../patterson-s-f-statistics/drift-model.md)
with the canonical [lineage weights](admixture-graph.md). The model excludes
mutation, selection and shared hidden update randomness.
It is an exact binomial model, not a diffusion approximation.

## Depends on

- [Admixture graph](admixture-graph.md)
- [Canonical drift model](../patterson-s-f-statistics/drift-model.md)

## Proof depends on

- [Single-root stochastic-graph realization](admixture-graphs-as-graphical-models-soraggi-wiu.md)
- [Neutral tree and arbitrary-start binomial construction](../patterson-s-f-statistics/neutral-wright-fisher-on-a-tree-realizes-the-dri.md)

## Expansion

Given the entire parental history, the child update has conditional mean
$q$. Hence $\eta$ is orthogonal to all previously generated increments.
The incoming mixing edges introduce no noise, and the outgoing edge
carries all the stated resampling variance. Repeated acyclic substitution
gives the graph weights. In the pulse diamond the resulting check is
$f_3(X;A,B)=-\alpha(1-\alpha)f_2(A,B)+\mathbb E\eta^2$;
the corresponding noiseless node has the same expression without the
last term.

Copying the same nondegenerate realized noise to both incoming edges
would not make them orthogonal: the cross moment of $c\eta$ and $d\eta$
is $cd\mathbb E\eta^2$, nonzero for nonzero $c,d$. This does **not** prove
that every alternative incoming-edge representation is impossible.
For example, with $p_A=p_B=1/2$, $\alpha=1/2$, $M=2$, independent
Bernoulli$(1/2)$ variables $Y_A,Y_B$ give
$(Y_A+Y_B)/2\sim\operatorname{Binomial}(2,1/2)/2$ with independent,
nondegenerate incoming increments $Y_A-1/2,Y_B-1/2$.
The child-edge convention here fixes a representation and avoids duplicating
one noise; it is not a theorem of unique noise allocation.

## Sources

- S. Soraggi and C. Wiuf, *General theory for stochastic admixture graphs and F-statistics* (2019), <https://doi.org/10.1016/j.tpb.2018.12.002>, <https://arxiv.org/abs/1807.07593>, Example 2 and Theorem 3. Example 2 blends contributions after edge evolution; the extra child edge explicitly implements the post-mixture binomial resampling specified here.
