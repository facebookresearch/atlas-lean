# Backtracking maximal-munch tokenization is quadratic

Let a lexer specification be given by regular expressions for its token classes, recognized by one deterministic finite automaton, and consider the standard algorithm for [maximal-munch tokenization](maximal-munch-lexing-with-rule-priority.md): from the current position, run the automaton until it cannot move or the input ends, remembering the last position at which it was in a final state; report the token ending there, and restart from the next position, backtracking over the characters read beyond it. The token classes do not contain the empty string, and the algorithm reports failure if no prefix of the remaining input is a token.

**Theorem.** This algorithm can take time quadratic in the length of the input. With the two token classes $abc$ and $(abc)^*d$ and the input $(abc)^m$, it reads to the end of the input looking for a token of the second class before reporting each of the $m$ tokens $abc$, and rewinds its next-unread position over the $3(m - k)$ characters read beyond the $k$-th token, so it performs $\Theta(m^2)$ steps.

The same holds whether the automaton is deterministic or nondeterministic, and whether backtracking returns to the last final state directly or by an explicit search of a stack of visited states.

## Depends on

- [Maximal-munch lexing with rule priority](maximal-munch-lexing-with-rule-priority.md)

## Sources

- T. Reps, "‘Maximal-munch’ tokenization in linear time", *ACM Transactions on Programming Languages and Systems*, 1998; author's version at <https://research.cs.wisc.edu/wpis/papers/toplas98b.pdf>: Section 1 (the backtracking method recommended in compiler textbooks, the example with the token classes $abc$ and $(abc)^*d$ on the input $(abc)^m$ and its $\Theta(m^2)$ behavior, footnote 2 with the simpler example $a$ and $a^*b$) and the remark, with footnote 3, that both backtracking methods are quadratic in the worst case.
