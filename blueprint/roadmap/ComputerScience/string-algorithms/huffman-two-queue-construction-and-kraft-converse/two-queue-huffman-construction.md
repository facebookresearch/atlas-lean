# Van Leeuwen's two-queue Huffman construction

If the $n$ symbol weights are nonnegative and given in nondecreasing order, Huffman's algorithm can be run with two FIFO queues instead of a priority queue: one queue holds the unmerged leaves in order, the other the merged internal nodes in creation order, and each step removes the two lightest fronts among the queues and appends their merge to the second queue. The second queue stays sorted, because consecutive merged sums are nondecreasing for nonnegative weights, so the result is a valid Huffman tree, hence optimal, and it is built in $O(n)$ word-RAM instructions; for unsorted input, sorting first gives $O(n \log n)$.

## Proof sketch

If merges $m_1, m_2$ are created in this order then $w(m_1) \le w(m_2)$, since $m_2$'s two parts were available when $m_1$ was formed or are at least as heavy as $m_1$'s parts.

## Depends on

- [Huffman's algorithm](../../../InformationTheory/source-coding/huffman-coding/huffman.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Huffman trees beat every prefix-free code](../../../InformationTheory/source-coding/huffman-coding/huffman-optimal-prefix-free.md)

## Sources

- J. van Leeuwen, "On the Construction of Huffman Trees", Automata, Languages and Programming (ICALP 1976), Edinburgh University Press, 1976.
- D. A. Huffman, "A Method for the Construction of Minimum-Redundancy Codes", Proceedings of the IRE 40(9), 1952.
