# Linear-time parsing of parsing expression grammars

For every [parsing expression grammar](parsing-expression-grammars.md) there is a parser that runs in time linear in the length of the input on a random-access machine.

**Proof idea.** Repetition and predicates can be eliminated, reducing the grammar to an equivalent grammar in Birman's generalized top-down parsing language (GTDPL), whose rules are $A \leftarrow \varepsilon$, $A \leftarrow a$, $A \leftarrow f$ and $A \leftarrow B[C, D]$, meaning: try $B$; on success continue with $C$, and on failure try $D$ at the original position. A GTDPL grammar is parsed by tabulating, for each nonterminal and each input position, the result of applying the nonterminal there, which takes a constant amount of work per table entry for a fixed grammar.

## Depends on

- [Parsing expression grammars](parsing-expression-grammars.md)

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>: Section 4.4 (reduction to TDPL and GTDPL) and Section 4.4.1, the corollary that a linear-time parser can be constructed for any PEG on a reasonable random-access memory machine, by reduction to GTDPL and the tabular parsing technique of Aho and Ullman.

## Expansion

This page needs a source check before it is ready: the reduction steps of Sections 4.1–4.3 (elimination of repetition and predicates) and the exact form of GTDPL rules in Section 4.4 have to be checked, together with whether the corollary assumes a well-formed or complete grammar.
