# State-transition specification of a data structure

A *state-transition specification* $D$ of a data structure consists of a set $\mathsf{State}$ of abstract states, a set $\mathsf{Op}$ of operations, for each $o \in \mathsf{Op}$ a result set $\mathsf{Res}(o)$, an admissibility predicate $\mathsf{valid}(s, o)$, and a transition relation $\mathsf{step}(s, o) \subseteq \mathsf{State} \times \mathsf{Res}(o)$. A specification is *deterministic* if $\mathsf{step}(s, o) = \{f(s, o)\}$ is the graph of a function $f$.

An *adaptive client* is a finite tree whose internal nodes issue an operation $o$ and branch on its result. A client is *admissible* from $s$ if every issued operation is admissible and the continuation is admissible from every outcome $(s', a) \in \mathsf{step}(s, o)$ (demonic choice for the caller). A *valid transcript* from $s_0$ is a finite sequence $(o_1, a_1), \dots, (o_m, a_m)$ for which there are states $s_0, s_1, \dots, s_m$ with $\mathsf{valid}(s_{i-1}, o_i)$ and $(s_i, a_i) \in \mathsf{step}(s_{i-1}, o_i)$.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. E. Knuth, "The Art of Computer Programming, Volume 1: Fundamental Algorithms", 3rd edition, Addison-Wesley, 1997.
