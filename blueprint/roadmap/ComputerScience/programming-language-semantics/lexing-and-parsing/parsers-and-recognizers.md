# Parsers and recognizers

Fix a context-free grammar $G$ with start symbol $S$. A *parse tree* for a word $w$ is a derivation tree of $G$ with root $S$ and yield $w$. More generally, each derivation of $w$ may produce a *semantic value* $v$, written $S \xrightarrow{v} w$.
- A *recognizer* for $G$ is a decision procedure for membership $w \in L(G)$.
- A *parser* for $G$ maps each input to a parse tree, or a semantic value, or to *reject*. It is *sound* if every tree or value it returns for $w$ comes from a derivation $S \xrightarrow{v} w$, that is, it accepts only valid inputs. It is *complete* if it returns some tree or value whenever $w \in L(G)$.

**Theorem.**
1. Erasing the output of a sound and complete parser, so that it answers *accept* whenever it returns a tree or a semantic value, gives a recognizer for $L(G)$.
2. If $G$ is unambiguous, so that every $w \in L(G)$ has exactly one parse tree, then a sound and complete parser whose results are parse trees returns that tree on every $w \in L(G)$. Its output is then determined by $G$ alone.
3. A recognizer's yes-or-no answer carries no parse tree. For example, the CYK and Earley recognition tables certify membership, and producing a parse tree requires an extra step that reads a tree back from the table.

**Proof.**
1. Soundness gives $w \in L(G)$ whenever the parser returns a result, and completeness gives a result whenever $w \in L(G)$.
2. By soundness, the returned tree is a parse tree of $w$, and there is only one.
3. Membership is a single bit, while a parse tree records a derivation.

For LR(1) parsers, Jourdan, Pottier and Leroy prove soundness for every automaton run by their interpreter (Theorem 1). Completeness holds, given enough fuel, for automata that pass both the safety validator, which rules out internal errors (Theorem 2), and the completeness validator (Theorem 3).

## Background

- [Safety validation of LR(1) automata](safety-validation-of-lr-1-automata.md)
- [Completeness validation of LR(1) automata](completeness-validation-of-lr-1-automata.md)
- [An unambiguous expression grammar and its abstract syntax](an-unambiguous-expression-grammar-and-its-abstract.md)

## Sources

- J.-H. Jourdan, F. Pottier and X. Leroy, "Validating LR(1) parsers", *ESOP 2012*, LNCS 7211, Springer, 2012, pp. 397–416, <https://xavierleroy.org/publi/validated-parser.pdf>:
    - the abstract, which distinguishes soundness, completeness and unambiguity;
    - Sections 2.1–2.3: grammars whose symbols carry semantic values, the remark that parsing constructs a value rather than only recognizing, and the derivation relation $X \xrightarrow{v} w$;
    - Section 3: soundness (only valid inputs are accepted), safety and completeness (all valid inputs are accepted), with Theorem 1 (soundness) and Theorem 3 (completeness).

    The bridge facts are proved here.
