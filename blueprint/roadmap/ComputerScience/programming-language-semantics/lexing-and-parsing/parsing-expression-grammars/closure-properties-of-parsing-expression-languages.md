# Closure properties of parsing expression languages

1. The class of [parsing expression languages](parsing-expression-grammars.md) is closed under union, intersection and complement. For grammars $G_1$ and $G_2$ over the same terminals with disjoint nonterminals and start expressions $e_S^1$ and $e_S^2$, the grammar with both rule sets and start expression $e_S^1 / e_S^2$, $\&e_S^1\,e_S^2$ or $!e_S^1$ recognizes $L(G_1) \cup L(G_2)$, $L(G_1) \cap L(G_2)$ or $V_T^* \setminus L(G_1)$, respectively.
2. The class of parsing expression languages includes languages that are not context-free. The grammar with rules

    $$A \leftarrow a A b / \varepsilon, \qquad B \leftarrow b B c / \varepsilon, \qquad D \leftarrow \&(A\,!b)\;a^*\,B\;!.$$

    and start expression $D$ recognizes $\{a^n b^n c^n \mid n \ge 0\}$.

## Depends on

- [Parsing expression grammars](parsing-expression-grammars.md)

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>, Section 3.4: the theorem on closure under union, intersection and complement with its proof, and the theorem that the parsing expression languages include non-context-free languages, with the grammar for $a^n b^n c^n$.
