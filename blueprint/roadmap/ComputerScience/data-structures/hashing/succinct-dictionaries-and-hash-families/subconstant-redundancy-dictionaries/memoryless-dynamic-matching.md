# Memoryless dynamic matching of balls to bins

Let $n' \le U'$. A *dynamic matching scheme* assigns to every active set $A \subseteq [U']$ of balls with $|A| \le n'$ an injective map from $A$ into the bins $[n']$ that depends only on $A$ and on randomness fixed at initialization (it is *memoryless*: history independent). The cost of an update (inserting or deleting a ball) is the number of balls whose bin changes. This is Problem 3.1 of Li, Liang, Yu and Zhou with the bin set fixed to $[n']$; their problem also lets the bin set $B$ change, under the promise $|A| \le |B|$.

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- A. Berger, W. Kuszmaul, A. Polak, J. Tidor and N. Wein, "Memoryless Worker-Task Assignment with Polylogarithmic Switching Cost", Proceedings of the 49th International Colloquium on Automata, Languages and Programming (ICALP), LIPIcs 229, pp. 19:1-19:19, 2022.
