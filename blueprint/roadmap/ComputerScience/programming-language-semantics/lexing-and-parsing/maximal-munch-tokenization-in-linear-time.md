# Maximal-munch tokenization in linear time

Let $M = (Q, \Sigma, \delta, q_0, F)$ be a deterministic finite automaton recognizing the union of the token classes of a lexer specification. Maximal-munch tokenization of an input of length $n$, which repeatedly takes the longest prefix of the remaining input that is a token, can always be performed in time $O(n)$, with the constant depending on $|Q|$.

**Algorithm.** Run the [backtracking tokenizer](backtracking-maximal-munch-tokenization-is-quadra.md) with an explicit stack of pairs $\langle q, i\rangle$ of a state and an input position, and add a table $\mathit{failed\_previously}[q, i]$. When backtracking pops a pair, record it in the table: from state $q$ at position $i$ the scan cannot reach a final state, so it cannot lead to a longer token. During scanning, stop as soon as the current pair is in the table. Each of the $O(|Q| \cdot n)$ pairs is entered in the table at most once, and each is popped from the stack at most once, so the total work is $O(n)$ for a fixed automaton.

## Depends on

- [Maximal-munch lexing with rule priority](maximal-munch-lexing-with-rule-priority.md)

## Proof depends on

- [Backtracking maximal-munch tokenization is quadratic](backtracking-maximal-munch-tokenization-is-quadra.md)

## Sources

- T. Reps, "‘Maximal-munch’ tokenization in linear time", *ACM Transactions on Programming Languages and Systems*, 1998; author's version at <https://research.cs.wisc.edu/wpis/papers/toplas98b.pdf>: the abstract (maximal-munch tokenization can always be performed in time linear in the size of the input), Figure 1 and its discussion (the stack-based backtracking tokenizer, Figure 1(a), and the linear-time version with the table $\mathit{failed\_previously}[q, i]$, Figure 1(b)), and the argument that, since there are only $O(n)$ pairs $\langle q, i\rangle$, the running time is $O(n)$ with a constant depending on $|Q|$.
