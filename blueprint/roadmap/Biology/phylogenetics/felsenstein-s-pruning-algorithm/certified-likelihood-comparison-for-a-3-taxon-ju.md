# Certified likelihood comparison for a three-taxon Jukes–Cantor example

This node covers a certified numerical comparison of two likelihoods. Fix an alignment of $m$ sites on three taxa $X=\{a,b,c\}$ with bases in $\{A,C,G,T\}$, and two rooted trees $T_1,T_2$ on $X$ with fixed nonnegative rational branch lengths (no optimization over lengths). Under the Jukes–Cantor model with unit rate, a branch of length $t$ has the [transition probabilities](../jukes-cantor-model/jc-prob.md)

$$P_{ii}(t)=\tfrac14+\tfrac34e^{-4t/3},\qquad P_{ij}(t)=\tfrac14-\tfrac14e^{-4t/3}\quad(i\ne j),$$

the root base is uniform, and sites are independent. The log-likelihood of $T_k$ is $\ell(T_k)=\sum_{s=1}^m\log L_s(T_k)$, where the site likelihood $L_s(T_k)$ is computed by [Felsenstein's pruning recursion](prune-eq-brute-lik.md). The target is a procedure that returns, for each $k$, an interval $[\underline\ell_k,\overline\ell_k]$ with $\underline\ell_k\le\ell(T_k)\le\overline\ell_k$, computed from exact rational pruning with certified rational bounds on each $e^{-4t/3}$ and a floating-point enclosure of the sum of logarithms, together with the decision rule: if $\overline\ell_1<\underline\ell_2$ then $T_2$ has strictly higher likelihood than $T_1$ (and symmetrically). When the two intervals overlap, the rule makes no claim.

## Depends on

- [Jukes–Cantor transition probability](../jukes-cantor-model/jc-prob.md)
- [Felsenstein's pruning algorithm computes the likelihood conditioned on the root state](prune-eq-brute-lik.md)

## Expansion

A full treatment splits this target into separately stated results:

- certified rational lower and upper bounds for $e^{-4t/3}$ at rational $t\ge0$, and monotonicity of the pruning recursion in each transition probability, so that interval inputs give an interval enclosing each $L_s(T_k)$;
- an enclosure of $\sum_s\log L_s(T_k)$ that accounts for both the interval of each $L_s$ and the rounding of the logarithms and of the floating-point summation;
- soundness of the disjoint-enclosure decision rule, which is immediate from the two enclosures;
- a worked instance: enclosures computed for a four-site alignment on three taxa.

Prerequisites:

- [Certified enclosure for a rounded recursive log-likelihood sum](../../../ComputerScience/algebraic-and-numerical-algorithms/rounding-error-analysis/abs-rsum-sub-sum-le.md)
- [Felsenstein's pruning algorithm computes the likelihood conditioned on the root state](prune-eq-brute-lik.md)
- [HKY85 matrix is a rate matrix](../time-reversible-nucleotide-substitution-models/is-rate-matrix-hky-rate.md) (the Jukes–Cantor rate matrix is the HKY85 case with $\kappa=1$ and uniform base frequencies, up to the time scale)

## Sources

- J. Felsenstein, *Evolutionary trees from DNA sequences: a maximum likelihood approach*, Journal of Molecular Evolution 17 (1981), 368–376, <https://pubmed.ncbi.nlm.nih.gov/7288891/> (pruning; background).
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM (2002) (floating-point model).
