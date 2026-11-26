# Undecidable problems for parsing expression grammars

For arbitrary [parsing expression grammars](parsing-expression-grammars.md):
1. it is undecidable whether $L(G)$ is empty;
2. it is undecidable whether two grammars recognize the same language;
3. it is undecidable whether a grammar is complete, that is, whether its start expression succeeds or fails on every input string.

**Proof sketch.** Part 1 reduces Post's correspondence problem: for an instance $(x_1, y_1), \dots, (x_n, y_n)$, with fresh marker terminals $a_1, \dots, a_n$, the rules $A \leftarrow x_1 A a_1 / \dots / x_n A a_n / \varepsilon$, $B \leftarrow y_1 B a_1 / \dots / y_n B a_n / \varepsilon$ and $D \leftarrow \&.\;\&(A\,!.)\;B\,!.$ give a grammar whose language is nonempty exactly when the instance has a solution. Part 2 follows by comparing with a grammar for the empty language. Part 3: adding a rule $A' \leftarrow \&e_S\,A'$ with start expression $A'$ gives a grammar that is complete exactly when $L(G)$ is empty.

## Depends on

- [Parsing expression grammars](parsing-expression-grammars.md)

## Proof depends on

- [Closure properties of parsing expression languages](closure-properties-of-parsing-expression-languages.md)

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>: Section 3.4 (the theorems that emptiness of $L(G)$ and equivalence of two PEGs are undecidable, with the reduction from Post's correspondence problem) and Section 3.5 (the theorem that completeness is undecidable, with its proof).
