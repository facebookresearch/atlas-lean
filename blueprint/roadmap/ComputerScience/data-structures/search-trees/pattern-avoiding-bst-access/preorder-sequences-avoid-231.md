# Preorder sequences of BSTs are exactly the 231-avoiding permutations

A permutation $X$ of $[n]$ is the preorder sequence of some binary search tree on $[n]$ if and only if $X$ avoids the pattern $231$. Consequently the traversal conjecture is equivalent to the statement that, from any initial tree on $[n]$, splay trees access every $231$-avoiding permutation of $[n]$ at total cost $O(n)$.

## Proof sketch

In a preorder sequence with root $x_1$, all keys smaller than $x_1$ precede all larger keys. An occurrence of $231$ is a key $a$, then a larger key $b$, then a key $c$ smaller than $a$; at the root of the smallest subtree containing all three, $c$ lies in the left part (or is the root) and $b$ in the right part, yet $c$ comes after $b$, which is impossible. Conversely, if $X$ avoids $231$, then after $x_1$ every key smaller than $x_1$ precedes every larger key, since otherwise $x_1$, a larger key and a later smaller key would form a $231$; so $X$ splits into two $231$-avoiding blocks, which by induction are preorders of the left and right subtrees.

## Depends on

- [Classical pattern containment in a sequence](../../../../Combinatorics/permutations/permutation-patterns/cyclic-pattern-avoiding-stack-sorting/contains-pattern-seq.md)
- [The pattern $231$](../../../../Combinatorics/permutations/permutation-patterns/permutations-counted-by-odd-indexed-fibonacci-nu/pat231.md)
- [Deque and traversal conjectures for splay trees](../distribution-sensitive-bst-bounds/deque-and-traversal-conjectures.md)

## Sources

- Parinya Chalermsook, Mayank Goswami, László Kozma, Kurt Mehlhorn, Thatchaphol Saranurak, "Pattern-Avoiding Access in Binary Search Trees", FOCS (2015), arXiv:1507.06953.
- Donald E. Knuth, "The Art of Computer Programming, Volume 1: Fundamental Algorithms", 3rd ed., Addison-Wesley (1997).
