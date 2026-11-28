# Consistency of product-based fuzzy description logic ontologies is undecidable

For the fuzzy description logic $*$-ALE with general concept inclusions, interpreted with any continuous t-norm whose first summand is the product t-norm on $[0, q]$ for a rational $q$, consistency with respect to witnessed, quasi-witnessed, weakly witnessed, strongly witnessed or finite models is undecidable.

**Theorem (Baader and Peñaloza).** Let $\otimes$ be a continuous t-norm that $q$-starts with the product t-norm for some rational $q \in (0, 1]$, interpreting conjunction in [$*$-ALE](fuzzy-dl-with-residuated-implication.md), with implication interpreted by its residuum. Then each of the following problems is undecidable for $*$-ALE ontologies (ABox and TBox of graded GCIs):

1. witnessed consistency (Corollary 7);
2. weakly witnessed consistency and quasi-witnessed consistency (Corollary 8);
3. strongly witnessed consistency and consistency with respect to finite models (Corollary 10).

In particular this holds for the product t-norm itself ($q = 1$). Whether consistency with respect to all models is undecidable under these t-norms is left open in the source.

## Depends on

- [Fuzzy description logic with residuated implication](fuzzy-dl-with-residuated-implication.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the Post correspondence problem. Words over $\{1, \dots, m\}$ index the elements of a tree-shaped model, and for each node $\mu$ the degrees of two concept names encode the concatenations $v_\mu$ and $w_\mu$ as numbers: $A^\mathcal{I}(\delta_\mu) = q \cdot 2^{-v_\mu}$ and $B^\mathcal{I}(\delta_\mu) = q \cdot 2^{-w_\mu}$, where words over an alphabet of size $s$ are read as numbers in base $s + 1$, so that concatenation $uu'$ corresponds to $u \cdot (s+1)^{|u'|} + u'$. On $[0, q]$ the t-norm acts as rescaled multiplication and the residuum as rescaled division, which lets GCIs force, for each node and each pair $(v_i, w_i)$, a successor encoding the extended words. The ontology $\mathcal{O}_P$ always has a witnessed model, and adding a GCI that forces $A^\mathcal{I} \neq B^\mathcal{I}$ everywhere makes it inconsistent exactly when $P$ has a solution. For strongly witnessed models a different ontology is used, which has a strongly witnessed model iff it has a finite one.

## Sources

- F. Baader and R. Peñaloza, "On the undecidability of fuzzy description logics with GCIs and product t-norm", in *Frontiers of Combining Systems (FroCoS 2011)*, Lecture Notes in Computer Science 6989, Springer, 2011, pp. 55–70, doi:10.1007/978-3-642-24364-6_5; read as the open-access copy <https://boa.unimib.it/bitstream/10281/257917/1/BaPe-FroCoS11.pdf>: Theorem 6 and Corollaries 7, 8 and 10, with Lemma 5 and Theorem 9.
