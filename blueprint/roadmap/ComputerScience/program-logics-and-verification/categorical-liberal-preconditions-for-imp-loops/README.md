# Categorical liberal preconditions for IMP loops

Liberal preconditions describe partial correctness and form a greatest fixed point. The categorical loop uses exit and continuation branches, with universal relational preimages for assertions.

The IMP semantics follow [Nipkow and Klein, Concrete Semantics](https://concrete-semantics.cs.tum.edu/concrete-semantics.pdf), including its treatment of total correctness in section 12.5.

- [Relational liberal preconditions for IMP](liberal-pre-command-rel.md)
- [Hoare derivability as a liberal-preimage inclusion](derivable-iff-subset-liberal-pre.md)
- [Guarded liberal while transformer](while-step.md)
- [Categorical feedback gives the guarded while step](feedback-step-loop-body.md)
- [Hidden safety equals the while liberal precondition](safe-invariant-loop-body.md)
- [While liberal preconditions are greatest fixed points](wlp-while-eq-gfp.md)
- [Coinduction for liberal while preconditions](while-coinduction.md)
