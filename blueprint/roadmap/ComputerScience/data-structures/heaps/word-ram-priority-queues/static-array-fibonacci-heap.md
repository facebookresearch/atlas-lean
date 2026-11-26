# Static-array Fibonacci heap on the Word RAM

There is a word-RAM implementation of the indexed min-priority queue on $n$ handles in $9n + 1$ words, and of the min-priority queue with handles in $11 n + 1$ words, by a Fibonacci heap stored in static arrays, with potential $80 \cdot (\text{number of roots} + 2 \cdot \text{number of marked nodes})$ and initial potential $0$. Initialization takes at most $421$ instructions on zeroed memory (or $421(n+1)$ on arbitrary memory), and any sequence of $m_q$ queries, $m_{\mathrm{ins}}$ insertions, $m_{\mathrm{dec}}$ key decreases and $m_{\mathrm{ext}}$ minimum extractions executes in at most

$$
421 \left(m_q + m_{\mathrm{ins}} + m_{\mathrm{dec}} + m_{\mathrm{ext}} (\lfloor \log_2 n \rfloor + 1)\right)
$$

instructions.

## Proof sketch

Insertion, queries and key decrease cost $O(1)$ amortized: a cut adds a root and cascading cuts unmark nodes, paid by the potential. Extraction consolidates the root list through a degree-indexed table; the maximum degree is $O(\log n)$ by the Fibonacci rank bound, so its amortized cost is $O(\log n)$.

## Depends on

- [Fibonacci heap](../fibonacci-heap/fibonacci-heap.md)
- [Bounded min-priority queue with handles](min-priority-queue-with-handles.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Rank bound and amortized costs of Fibonacci heaps](../fibonacci-heap/rank-bound-and-amortized-costs-of-fibonacci-heaps.md)
- [Potential method: amortized costs bound actual costs](../../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- M. L. Fredman and R. E. Tarjan, "Fibonacci Heaps and Their Uses in Improved Network Optimization Algorithms", Journal of the ACM 34(3), 1987.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
