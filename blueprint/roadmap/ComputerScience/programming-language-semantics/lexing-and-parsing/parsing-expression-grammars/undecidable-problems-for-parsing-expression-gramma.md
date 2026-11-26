# Undecidable problems for parsing expression grammars

For arbitrary [parsing expression grammars](parsing-expression-grammars.md):
1. it is undecidable whether $L(G)$ is empty;
2. it is undecidable whether two grammars recognize the same language;
3. it is undecidable whether a grammar is complete, that is, whether its start expression succeeds or fails on every input string.

**Proof sketch.** Part 1 reduces [Post's correspondence problem](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md): for an instance $(x_1, y_1), \dots, (x_n, y_n)$, with fresh marker terminals $a_1, \dots, a_n$, take the rules $A \leftarrow a_1 A x_1 / \dots / a_n A x_n / \varepsilon$, $B \leftarrow a_1 B y_1 / \dots / a_n B y_n / \varepsilon$ and $D \leftarrow \&.\;\&(A\,!.)\;B\,!.$ with start expression $D$. Each recursive call follows a marker, so $A$ consumes a whole nonempty input exactly when it has the form $a_{i_1} \cdots a_{i_m}\, x_{i_m} \cdots x_{i_1}$, and likewise for $B$; hence the language is nonempty exactly when the instance has a solution. Part 2 follows by comparing with a grammar for the empty language. Part 3: the grammar of part 1 is [well-formed](well-formed-parsing-expression-grammars-are-comple.md), since every recursive call is preceded by a terminal, and hence complete, so emptiness is undecidable already for complete grammars. For a complete grammar $G$, add a rule $A' \leftarrow \&e_S\,A'$ and take $A'$ as start expression: if $e_S$ matches some input, $A'$ loops on it and does not handle it, while if $L(G)$ is empty, $e_S$ fails on every input and so does $A'$. So the new grammar is complete exactly when $L(G)$ is empty. Without completeness of $G$ this equivalence fails: an input that $e_S$ does not handle is not handled by $A'$ either.

## Depends on

- [Parsing expression grammars](parsing-expression-grammars.md)

## Proof depends on

- [Closure properties of parsing expression languages](closure-properties-of-parsing-expression-languages.md)
- [Well-formed parsing expression grammars are complete](well-formed-parsing-expression-grammars-are-comple.md)
- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>: Section 3.4 (the theorems that emptiness of $L(G)$ and equivalence of two PEGs are undecidable, with the reduction from Post's correspondence problem; the printed rules $A \leftarrow x_1 A a_1 / \dots$ place the markers after the recursive call and loop on instances with an empty $x_i$ or $y_i$, such as $(\varepsilon, b), (a, a)$, so the marker-first rules are written out here) and Section 3.5 (the theorem that completeness is undecidable, with its proof, which tacitly assumes $G$ complete) and Section 3.6 (well-formed grammars are complete). The restriction to complete grammars in part 3 is written out here.
