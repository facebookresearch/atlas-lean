# Word-addressed memory as a specification

The *word memory* specification with word size $w$ has as state a map from addresses $a < 2^w$ to $w$-bit words (all zero initially) together with an allocation frontier $F$ (initially $0$), and operations $\mathrm{read}(a)$ and $\mathrm{write}(a, v)$ for $v < 2^w$, admissible only at addresses $a < F$ below the frontier, and $\mathrm{alloc}(k)$, which returns the current frontier and advances it by $k$, admissible when the new frontier still fits in a word ($F + k < 2^w$). Every admissible address is therefore below $2^w$ and representable in one word. Each operation is charged one unit. Data structures built from memory operations, such as records of named cells and field arrays, are refinements of their abstract specifications over this one, and their memory cost bounds compose with Word-RAM simulations of the memory operations.

## Depends on

- [State-transition specification of a data structure](state-transition-specification.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. E. Knuth, "The Art of Computer Programming, Volume 1: Fundamental Algorithms", 3rd edition, Addison-Wesley, 1997.
