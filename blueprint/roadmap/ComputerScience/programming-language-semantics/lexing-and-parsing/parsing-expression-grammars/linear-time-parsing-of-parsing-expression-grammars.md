# Linear-time parsing of parsing expression grammars

For every [parsing expression grammar](parsing-expression-grammars.md) there is a parser that runs in time linear in the length of the input on a random-access machine.

**Proof idea.** Every grammar is reduced directly to an equivalent grammar in Birman's generalized top-down parsing language (GTDPL), whose rules are $A \leftarrow \varepsilon$, $A \leftarrow a$, $A \leftarrow f$ with $f = !\varepsilon$, and $A \leftarrow B[C, D]$, standing for $B\,C / !B\,D$. With new nonterminals $S \leftarrow e_S$, $E \leftarrow \varepsilon$ and $F \leftarrow f$, each nonconforming rule is rewritten: $A \leftarrow B$ becomes $A \leftarrow B[E, F]$; $A \leftarrow e_1 e_2$ becomes $A \leftarrow B[C, F]$, $A \leftarrow e_1 / e_2$ becomes $A \leftarrow B[E, C]$, $A \leftarrow e^*$ becomes $A \leftarrow B[A, E]$ and $A \leftarrow !e$ becomes $A \leftarrow B[F, E]$, with new rules $B \leftarrow e_1$ or $B \leftarrow e$ and $C \leftarrow e_2$. A GTDPL grammar is parsed by tabulating, for each nonterminal and each input position, the result of applying the nonterminal there, which takes a constant amount of work per table entry for a fixed grammar. No well-formedness assumption is needed for this reduction; the predicate elimination of Section 4.2, which assumes a well-formed grammar that does not accept the empty string, is not used.

## Depends on

- [Parsing expression grammars](parsing-expression-grammars.md)

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>: Section 4.4 (the definition of GTDPL and the theorem that any PEG reduces to an equivalent GTDPL grammar, with the five rewriting rules) and Section 4.4.1, the corollary that a linear-time parser can be constructed for any PEG on a reasonable random-access memory machine, by reduction to GTDPL and the tabular parsing technique of Aho and Ullman.

## Expansion

This page needs a source check before it is ready: the tabular parsing theorem for GTDPL of Aho and Ullman, which the corollary cites, has to be checked, including what the tabulated parser returns on inputs that the grammar does not handle.
