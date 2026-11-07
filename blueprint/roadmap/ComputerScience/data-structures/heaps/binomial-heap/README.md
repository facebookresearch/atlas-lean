# Binomial heap

## Lean

- [Binomial tree](binomial-tree.md)

## Binomial Tree

- [Rank of a binomial tree](rank.md)
- [Root of a binomial tree](root.md)
- [Children of a binomial tree](children.md)
- [Elements of a binomial tree](elements.md)
- [The root of a binomial tree is one of its elements](root-mem-elements.md)
- [Valid binomial tree](valid.md)
- [Singleton binomial heap](singleton.md)
- [Linking two binomial trees](link.md)
- [Linking binomial trees adds their elements](elements-link.md)
- [Singleton binomial trees are valid](valid-singleton.md)
- [Children of a valid binomial tree are valid](child-valid.md)
- [Child ranks of a valid binomial tree](children-ranks.md)
- [Size of a valid binomial tree](card-elements.md)
- [The rank of a valid binomial tree is logarithmic](rank-le-log2-card.md)
- [The root of a valid binomial tree is a lower bound](root-le.md)
- [Linking preserves binomial-tree validity](link-2.md)

## Lean

- [Valid binomial forest](valid-2.md)

## Binomial Forest

- [Elements of a binomial forest](elements-2.md)
- [Rank lower bound for a forest](ranks-at-least.md)
- [The empty forest is valid](valid-nil.md)
- [Validity of binomial forests passes to sublists](sublist.md)
- [Tree ranks in a valid forest are logarithmic](member-rank-le-log2-card.md)
- [A valid binomial forest has logarithmically many trees](length-le-log2-card-succ.md)
- [A valid binomial forest with no elements has no trees](length-eq-zero-of-card-eq-zero.md)
- [Carry insertion into a binomial forest](carry.md)
- [Melding binomial forests](meld-trees.md)
- [Melding binomial forests adds their elements](elements-meld-trees.md)
- [Melding preserves forest validity and rank lower bounds](meld-trees-correct.md)
- [Removing a minimum-root tree from a forest](remove-min-tree.md)
- [Removing a minimum-root tree](remove-min-tree-spec.md)
- [Reversed children of a valid binomial tree form a valid forest](valid-reverse-children.md)

## Lean

- [Binomial heap](binomial-heap.md)

## Binomial Heap

- [Elements of a binomial heap](elements-3.md)
- [Tree ranks in a binomial heap are logarithmic](rank-le-log2-card-2.md)
- [A binomial heap has logarithmically many trees](length-le-log2-card-succ-2.md)
- [Empty binomial heap](empty.md)
- [Melding binomial heaps](meld.md)
- [One-element binomial heap](singleton-2.md)
- [Insertion into a binomial heap](insert.md)
- [Minimum of a binomial heap](find-min.md)
- [Minimum deletion on a binomial forest](delete-min-trees.md)
- [Deleting the minimum of a binomial heap](delete-min.md)
- [Binomial heap deletion agrees with forest deletion](delete-min-trees-2.md)
- [Melding binomial heaps adds their elements](elements-meld.md)
- [Insertion into a binomial heap adds one occurrence](elements-insert.md)
- [The minimum lookup fails exactly on the empty binomial heap](find-min-eq-none-iff.md)
- [The minimum lookup of a binomial heap returns one of its elements](find-min-mem.md)
- [The minimum lookup of a binomial heap returns a lower bound](find-min-le.md)
- [Deleting the minimum fails only on the empty binomial heap](delete-min-eq-none-iff.md)
- [Deleting the minimum of a binomial heap removes one occurrence](delete-min-elements.md)
- [Deleting the minimum of a binomial heap splits its multiset](delete-min-cons-elements.md)
- [The value deleted from a binomial heap is a lower bound for its elements](delete-min-le.md)
