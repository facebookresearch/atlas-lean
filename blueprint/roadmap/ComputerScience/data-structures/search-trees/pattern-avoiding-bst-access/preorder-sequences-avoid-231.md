# Preorder sequences of BSTs are exactly the 231-avoiding permutations

A permutation $X$ of $[n]$ is the preorder sequence of some binary search tree on $[n]$ if and only if $X$ avoids the pattern $231$. Consequently the traversal conjecture concerns a subclass of $231$-avoiding access sequences, namely accessing such a sequence starting from an arbitrary initial tree.

## Proof sketch

If $X$ is a preorder sequence with root $x_1$, all keys smaller than $x_1$ precede all larger keys, so an occurrence of $231$ would need a larger key followed by a smaller one followed by an even smaller one within the same recursive block, contradicting the same property at the block's root; induct. Conversely, if $X$ avoids $231$, then after $x_1$ the keys smaller than $x_1$ must all precede the larger ones (else a larger key, then a smaller one, then relative to $x_1$ gives $231$), so $X$ splits into two $231$-avoiding blocks that are preorders of the left and right subtrees.

## Depends on

- [Pattern-avoiding access sequences](pattern-avoiding-access-sequence.md)
- [The pattern $231$](../../../../Combinatorics/permutations/permutation-patterns/permutations-counted-by-odd-indexed-fibonacci-nu/pat231.md)

## Proof depends on

- [Pattern-avoiding access sequences](pattern-avoiding-access-sequence.md)
- [The pattern $231$](../../../../Combinatorics/permutations/permutation-patterns/permutations-counted-by-odd-indexed-fibonacci-nu/pat231.md)

## Sources

- Parinya Chalermsook, Mayank Goswami, László Kozma, Kurt Mehlhorn, Thatchaphol Saranurak, "Pattern-Avoiding Access in Binary Search Trees", FOCS (2015), arXiv:1507.06953.
- Donald E. Knuth, "The Art of Computer Programming, Volume 1: Fundamental Algorithms", 3rd ed., Addison-Wesley (1997).
