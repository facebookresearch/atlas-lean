# Soundness of ioco test generation

Every test case generated from a specification $s$ by Tretmans's ioco test-generation algorithm is sound: every input-enabled implementation $i$ with $i \mathrel{\mathbf{ioco}} s$ passes it. Moreover the set of all test cases the algorithm can generate is exhaustive: an implementation passing all of them satisfies $i \mathrel{\mathbf{ioco}} s$.

## Depends on

- [The ioco conformance relation](the-ioco-conformance-relation.md)

## Sources

- J. Tretmans, "Model based testing with labelled transition systems", in *Formal Methods and Testing*, LNCS 4949, Springer, 2008
