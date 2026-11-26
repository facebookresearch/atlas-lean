# Parsing expression grammars

A *parsing expression grammar* (PEG) is a tuple $G = (V_N, V_T, R, e_S)$ of disjoint finite sets $V_N$ of nonterminals and $V_T$ of terminals, a function $R$ assigning to each nonterminal $A$ a parsing expression $R(A)$, written $A \leftarrow R(A)$, and a start expression $e_S$. *Parsing expressions* are built from $\varepsilon$, terminals $a$ and nonterminals $A$ by sequence $e_1 e_2$, *prioritized choice* $e_1 / e_2$, repetition $e^*$ and the *not-predicate* $!e$.

The interpretation is the least relation $(e, x) \Rightarrow (n, o)$ between an expression and an input $x \in V_T^*$ on one side, and a step count $n$ and an outcome $o$ on the other, where $o$ is either the prefix of $x$ consumed by a success or the failure symbol $f$, closed under these rules, in which $x, x_1, x_2, y$ range over $V_T^*$:
- $(\varepsilon, x) \Rightarrow (1, \varepsilon)$; $(a, a x) \Rightarrow (1, a)$; $(a, b x) \Rightarrow (1, f)$ for $b \ne a$, and $(a, \varepsilon) \Rightarrow (1, f)$;
- $(A, x) \Rightarrow (n + 1, o)$ if $(R(A), x) \Rightarrow (n, o)$;
- $(e_1 e_2, x_1 x_2 y) \Rightarrow (n_1 + n_2 + 1, x_1 x_2)$ if $(e_1, x_1 x_2 y) \Rightarrow (n_1, x_1)$ and $(e_2, x_2 y) \Rightarrow (n_2, x_2)$; $(e_1 e_2, x) \Rightarrow (n_1 + 1, f)$ if $(e_1, x) \Rightarrow (n_1, f)$; $(e_1 e_2, x_1 y) \Rightarrow (n_1 + n_2 + 1, f)$ if $(e_1, x_1 y) \Rightarrow (n_1, x_1)$ and $(e_2, y) \Rightarrow (n_2, f)$;
- $(e_1 / e_2, x y) \Rightarrow (n_1 + 1, x)$ if $(e_1, x y) \Rightarrow (n_1, x)$; $(e_1 / e_2, x) \Rightarrow (n_1 + n_2 + 1, o)$ if $(e_1, x) \Rightarrow (n_1, f)$ and $(e_2, x) \Rightarrow (n_2, o)$;
- $(e^*, x_1 x_2 y) \Rightarrow (n_1 + n_2 + 1, x_1 x_2)$ if $(e, x_1 x_2 y) \Rightarrow (n_1, x_1)$ and $(e^*, x_2 y) \Rightarrow (n_2, x_2)$; $(e^*, x) \Rightarrow (n_1 + 1, \varepsilon)$ if $(e, x) \Rightarrow (n_1, f)$;
- $(!e, x y) \Rightarrow (n + 1, f)$ if $(e, x y) \Rightarrow (n, x)$; $(!e, x) \Rightarrow (n + 1, \varepsilon)$ if $(e, x) \Rightarrow (n, f)$.

So the step count adds one for the rule applied to the step counts of the premises that were evaluated.

The expression $e$ *matches* $x$ if $(e, x) \Rightarrow (n, y)$ for some $n$ and $y \in V_T^*$, and *fails on* $x$ if $(e, x) \Rightarrow (n, f)$; it *handles* $x$ if it does one of these, and $G$ is *complete* if $e_S$ handles every string. The language $L(G)$ is the set of strings that $e_S$ matches, without having to consume them entirely, and a *parsing expression language* is the language of some PEG. The and-predicate $\&e$ abbreviates $!(!e)$, the any-terminal expression $.$ the choice of all terminals, $e?$ the choice $e / \varepsilon$ and $e^+$ the sequence $e\,e^*$.

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>: Section 3.1 (the definition of a PEG and of parsing expressions), Section 3.2 (desugaring of the concrete syntax), and Section 3.3 (the relation $\Rightarrow_G$ with its thirteen rules and their step counts, matching, failing, handling, completeness, and the definitions of $L(G)$ and of parsing expression languages).
