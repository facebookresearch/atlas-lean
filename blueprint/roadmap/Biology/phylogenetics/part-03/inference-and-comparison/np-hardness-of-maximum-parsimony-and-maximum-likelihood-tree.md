# NP-hardness of maximum parsimony and maximum likelihood tree reconstruction

This node collects hardness results for phylogenetic reconstruction, each as a decision or optimization problem with
its own model.

## Expansion

A sound expansion has separate pages for:

1. **Maximum parsimony:** given aligned sequences and an integer $k$, deciding whether some tree has parsimony score at most $k$
   is NP-complete (Graham and Foulds 1982; Day, Johnson and Sankoff 1986, by a reduction from vertex cover), with the
   character encoding stated.
2. **Ancestral maximum likelihood:** the decision version, under the stated substitution model, is NP-complete
   (Addario-Berry, Chor, Hallett, Lagergren, Panconesi and Wareham 2004, by a reduction from vertex cover).
3. **Maximum-likelihood trees:** under Neyman's two-state model, the problem "given a set $S$ of binary strings of equal
   length and a negative threshold $L$, is there a tree $T$ with $\log \Pr(S \mid T, p^*(S, T)) > L$", where $p^*(S, T)$ are
   edge substitution probabilities maximizing the likelihood on $T$, is NP-hard (Chor and Tuller, by a reduction from gap
   vertex cover on graphs of maximum degree $3$, which Berman and Karpinski proved NP-hard); the same holds under the
   Jukes–Cantor model. The encoding of $L$, which the source leaves informal, is fixed on the page.

## Depends on

- [Polynomial-time many-one reduction](../../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Related topics

- [Sankoff's algorithm computes the small-parsimony cost](../../small-parsimony-problem/sankoff-eq-inf.md)

## Sources

- B. Chor and T. Tuller, *Finding the maximum likelihood tree is hard*, J. ACM 53 (2006), 722–744; author preprint
  (submitted July 2005), Problem 5.1, Theorem 5.12 and Section 5.4 (maximum likelihood, two-state and Jukes–Cantor
  models), Theorem 5.3 (gap vertex cover, after Berman and Karpinski), and Section 1 (the parsimony results of Graham and
  Foulds and of Day, Johnson and Sankoff, and the ancestral maximum likelihood result of Addario-Berry et al., cited
  there). <http://www.cs.tau.ac.il/~bchor/ML.pdf>
