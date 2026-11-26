# The interpretation of a parsing expression grammar is a function

Let $G$ be a [parsing expression grammar](parsing-expression-grammars.md) with interpretation $\Rightarrow$.

1. If $(e, x) \Rightarrow (n, y)$ with $y \in V_T^*$, then $y$ is a prefix of $x$.
2. If $(e, x) \Rightarrow (n_1, o_1)$ and $(e, x) \Rightarrow (n_2, o_2)$, then $n_1 = n_2$ and $o_1 = o_2$: the relation is a partial function.
3. ($*$-loop condition.) If $(e, x) \Rightarrow (n_1, \varepsilon)$, then $e^*$ does not handle $x$: there are no $n_2, o_2$ with $(e^*, x) \Rightarrow (n_2, o_2)$.

Each part is proved by induction on step counts.

## Depends on

- [Parsing expression grammars](parsing-expression-grammars.md)

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>, Section 3.3: the three theorems following the definition of the relation $\Rightarrow_G$ (outputs are prefixes of the input, $\Rightarrow_G$ is a function, and the $*$-loop condition), with their proofs by induction on step counts.
