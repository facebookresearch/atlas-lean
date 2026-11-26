# Linking a client through methods is oracle interpretation

Let $p$ be an adaptive client of a specification $D$, viewed as an oracle program over $D$'s operations, and let a module implement each $D$-operation $o$ by a client $M_o$ of a lower interface $E$. The *linked* client, which replaces every call to $o$ by $M_o$, equals the interpretation of $p$ in the free monad of $E$ that answers each call $o$ with $M_o$. Consequently linking is associative (linking through two module layers equals linking through their composite), and every law of oracle interpretation (sequencing, composition, interpretation into probability or state monads) applies to linked clients.

## Proof sketch

Both linking and interpretation are defined by structural recursion on the client tree and agree on returns and on calls; associativity is the composition law of interpretations.

## Depends on

- [Refinement of a data-structure specification by an abstraction function](refinement-by-abstraction-function.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
