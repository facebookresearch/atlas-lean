# Closure properties of parsing expression languages

1. Let $G_1$ and $G_2$ be [parsing expression grammars](parsing-expression-grammars.md) over the same terminals with disjoint nonterminals and start expressions $e_S^1$ and $e_S^2$, and let $G'$ have both rule sets.
    - With start expression $\&e_S^1\,e_S^2$, $G'$ recognizes $L(G_1) \cap L(G_2)$.
    - If $G_1$ is complete, then with start expression $e_S^1 / e_S^2$ it recognizes $L(G_1) \cup L(G_2)$, and with start expression $!e_S^1$ it recognizes $V_T^* \setminus L(G_1)$.

    Completeness of $G_1$ cannot be dropped: for $A \leftarrow A$, $L(G_1)$ is empty, but $!A$ and $A / \varepsilon$ handle no input, so they recognize the empty language rather than $V_T^*$.
2. The class of parsing expression languages includes languages that are not context-free. The grammar with rules

    $$A \leftarrow a A b / \varepsilon, \qquad B \leftarrow b B c / \varepsilon, \qquad D \leftarrow \&(A\,!(a / b))\;a^*\,B\;!.$$

    and start expression $D$ recognizes $\{a^n b^n c^n \mid n \ge 0\}$: the predicate accepts exactly the inputs that begin with $a^n b^n$ followed by neither $a$ nor $b$, and $a^* B\,!.$ then requires the rest to be $b^n c^n$ and the end of the input.

## Depends on

- [Parsing expression grammars](parsing-expression-grammars.md)

## Proof depends on

- [The language $a^n b^n c^n$ is not context-free](../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/non-closure-of-context-free-languages/anbncn-lang-not-is-context-free.md)

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>, Section 3.4: the theorem on closure under union, intersection and complement with its proof, and the theorem that the parsing expression languages include non-context-free languages, with a grammar for $a^n b^n c^n$. The printed grammar uses $\&(A\,!b)$, which accepts the input $a$; the completeness hypothesis for union and complement and the corrected predicate are written out here. Section 5 mentions that every grammar can be converted into a complete one, by extension of a transformation of Birman, which would give closure of the class under union and complement; that conversion is not stated here.
