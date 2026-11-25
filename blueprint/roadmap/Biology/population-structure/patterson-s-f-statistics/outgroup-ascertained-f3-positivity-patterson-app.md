# Ascertainment in an outgroup keeps f3 of an unadmixed target nonnegative

Let populations $A, B, C$ descend from a root $R$ along a tree with no admixture, with allele frequencies evolving by [neutral binomial drift](neutral-wright-fisher-on-a-tree-realizes-the-dri.md) on its
edges from a random root frequency $r$, with no back or recurrent mutation, and let an outgroup $O$ split from the lineage above $R$. Let $S$ be an
ascertainment event with $\mu(S) > 0$ that is measurable with respect to $r$ and the outgroup lineage, and assume that the edge processes below $R$ are
conditionally independent of $S$ given $r$. Then under $\mu_S = \mu(\cdot \mid S)$ the increments $\delta_e$ on the edges below $R$ still have conditional mean zero
and zero cross moments given $r$, so

$$F_3(C; A, B) = \mathbb E_{\mu_S}\bigl[(c - a)(c - b)\bigr] = \sum_e \bigl(w(C, e) - w(A, e)\bigr)\bigl(w(C, e) - w(B, e)\bigr)\, \mathbb E_{\mu_S}[\delta_e^2] \ge 0 ,$$

where $w(X, e)$ is $1$ if $e$ lies on the path from $R$ to $X$ and $0$ otherwise; every term is nonnegative by the [termwise bound for a binary target](../negative-f3-as-a-test-of-admixture/sum-nonneg-of-target-binary.md). This is
cases (1) and (2) of Patterson et al., Appendix C, Theorem 1: no ascertainment, and ascertainment in an outgroup that split from $R$ more remotely
than $A, B, C$. Case (3), ascertainment of a heterozygote in one of $A, B, C$, is not covered, because that event depends on the edge processes below $R$; the
[conditioning example](../abba-baba-test-and-f-statistic-estimators/ascertainment-as-conditioning-breaks-the-second.md) shows what can then fail.

The hypotheses can hold with $0 < \mu(S) < 1$: let the frequency at the split of $O$ be $\frac12$, let the edges from the split to $O$ and to $R$ each make one update
$p \mapsto \mathrm{Binomial}(2, p)/2$, and let $S = \{0 < o < 1\}$ (polymorphic in the outgroup). Then $\mu(S) = \frac12$, $S$ depends only on the outgroup lineage, and by the
Markov property of drift on the tree the edges below $R$ are conditionally independent of $S$ given $r$.

## Depends on

- [Neutral binomial drift on a tree realizes the drift model](neutral-wright-fisher-on-a-tree-realizes-the-dri.md)

## Proof depends on

- [Termwise bound behind nonnegative f3 for a binary target](../negative-f3-as-a-test-of-admixture/sum-nonneg-of-target-binary.md)

## Related topics

- [Conditioning on an ascertainment event can correlate drift increments](../abba-baba-test-and-f-statistic-estimators/ascertainment-as-conditioning-breaks-the-second.md)

## Sources

- N. Patterson et al., "Ancient admixture in human history", Genetics 192 (2012), 1065–1093, <https://doi.org/10.1534/genetics.112.145037>, Appendix C, Theorem 1 and its proof (the main text's pointer to "Appendix D" refers to this theorem).
