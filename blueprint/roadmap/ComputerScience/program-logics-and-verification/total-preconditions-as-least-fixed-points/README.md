# Total preconditions as least fixed points

Total preconditions require a terminating execution satisfying the postcondition. Their while transformer has a least fixed point, excluding divergence without imposing a uniform iteration bound.

The IMP semantics follow [Nipkow and Klein, Concrete Semantics](https://concrete-semantics.cs.tum.edu/concrete-semantics.pdf), including its treatment of total correctness in section 12.5.

- [Guarded total-correctness transformer](while-step.md)
- [The total while precondition is a fixed point](while-step-wp.md)
- [Induction for total while preconditions](while-le-of-prefixed.md)
- [Total while preconditions are least fixed points](while-eq-lfp.md)
- [Total correctness is termination plus liberal correctness](iff-terminates-and-wlp.md)
