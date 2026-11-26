# Entropy-rate formula for the lower dimension of a self-similar measure

Let a nonempty finite alphabet carry probabilities $p_i>0$ summing to $1$ and real maps $f_i(x)=r_ix+t_i$ with $0<|r_i|<1$. Let $\mu$ be a Borel probability measure with $\mu=\sum_i p_i(f_i)_*\mu$. For each $n\geq1$, give each distinct affine map $g=f_{i_1}\circ\cdots\circ f_{i_n}$ mass $q_n(g)$ equal to the sum of $\prod_j p_{i_j}$ over words inducing exactly $g$. Write $h=\inf_{n\geq1}[-\sum_g q_n(g)\log_2 q_n(g)]/n$ and $\chi=-\sum_i p_i\log_2|r_i|$. Then $\inf\{\dim_{\rm H}E:E\text{ measurable},\ \mu(E)>0\}=\min(1,h/\chi)$. Signs, unequal contraction ratios and exact overlaps are allowed. This is the lower Hausdorff dimension of a measure, not the dimension of its support.

## Depends on
Finite probability-weighted affine compositions, their pushforward masses, and the infimum of Hausdorff dimensions over positive-measure sets.

## Proof depends on
Subadditivity of the composition entropy and matched upper and lower dimension estimates after identifying all exact coincidences of affine maps.

## Expansion
Construct the probability law on maps rather than words and prove the entropy-rate normalization. Isolate the multiscale lower dimension estimate and the concentration argument for the upper bound; preserve signed ratios and use one logarithmic base throughout.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SelfSimilar.lean#L65-L70) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/148.md).
