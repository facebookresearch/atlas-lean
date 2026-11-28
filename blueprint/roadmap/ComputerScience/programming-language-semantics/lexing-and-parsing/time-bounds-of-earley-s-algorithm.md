# Time bounds of Earley's algorithm

Let $G$ be a context-free grammar and consider the [Earley recognizer](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/earley-parser/earley-accepts.md) for $G$ as Earley implements it, with state sets $S_0, \dots, S_{n+1}$ for an input of length $n$, measured as the number of primitive steps of a random-access machine, with constants that depend on $G$ but not on $n$.

1. **General case.** The recognizer runs in time $O(n^3)$. The state set $S_i$ has $O(i)$ states, since only the origin component of a state depends on $i$. The scanner and the predictor take a bounded number of steps per state, and the completer takes $O(i)$ steps per state, so processing $S_i$ takes $O(i^2)$ steps.
2. **Unambiguous grammars.** If $G$ is [unambiguous](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/ambiguity-of-context-free-grammars/is-ambiguous.md) and *reduced*, meaning that every nonterminal appears in some derivation of some sentence (so that every nonterminal derives some terminal string), the recognizer runs in time $O(n^2)$. A state added to $S_i$ in two different ways by the completer would yield two derivation trees of one sentential form, and so an ambiguous sentence; hence the completer takes $O(i)$ steps per state set. The same bound holds for grammars of bounded ambiguity.

The bounds hold with or without look-ahead, and need no normal form of the grammar, in contrast with the cubic recognizer of Cocke, Younger and Kasami.

## Depends on

- [Acceptance by the Earley recognizer](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/earley-parser/earley-accepts.md)
- [Ambiguous grammar](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/ambiguity-of-context-free-grammars/is-ambiguous.md)

## Sources

- J. Earley, "An efficient context-free parsing algorithm", *Communications of the ACM* 13(2):94–102, 1970: the abstract and Section 5 (and Section 2 for the definition of a reduced grammar; "Time and Space Bounds": the random-access model, "The general case", with items (a)–(d) and the remark on look-ahead, and "Unambiguous grammars", with the argument for reduced unambiguous grammars and the remark on bounded ambiguity).
