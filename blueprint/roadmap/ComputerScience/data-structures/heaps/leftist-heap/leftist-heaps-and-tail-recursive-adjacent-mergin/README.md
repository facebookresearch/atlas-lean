# Leftist heaps and tail-recursive adjacent merging

## Leftist Heap datatype (concrete)

- [Leftist heap](lheap.md)
- [Number of nodes of a leftist heap](size.md)
- [Rank of a leftist heap](rank.md)
- [Multiset of elements of a leftist heap](mset-tree.md)
- [Lower bound on all elements of a heap](all-le.md)
- [Min-heap property](heap.md)
- [Leftist invariant with correct stored ranks](ltree.md)
- [Node constructor restoring the leftist property](make.md)
- [Fuel-based auxiliary merge of leftist heaps](merge-aux.md)
- [Merge of leftist heaps](merge.md)
- [Fuel-based auxiliary cost of merging](t-merge-aux.md)
- [Cost of merging leftist heaps](t-merge.md)
- [Non-tail-recursive adjacent merging of heaps](merge-adj.md)
- [Tail-recursive adjacent merging with an accumulator](merge-adj2.md)
- [Cost of non-tail-recursive adjacent merging](t-merge-adj.md)
- [Cost of tail-recursive adjacent merging](t-merge-adj2.md)

## merge_all variants using fuel to avoid complex termination proofs

- [Fuel-based merging of all heaps with tail-recursive passes](merge-all2-aux.md)
- [Singleton leftist heap](singleton.md)
- [Leftist heap from a list by tail-recursive merging](lheap-list2.md)

## Node construction and merge correctness

- [Combined multiset of a list of heaps](sum-mset.md)
- [Min-heap ordering of every heap in a list](heap-list.md)
- [Leftist invariant for every heap in a list](ltree-list.md)
- [Correctness and cost equivalence of tail-recursive heap construction](fdsa-chap15-ex04.md)
- [List-to-heap construction preserves the multiset](mset-lheap-list2.md)
- [List-to-heap construction gives a min-heap](heap-lheap-list2.md)
- [List-to-heap construction gives a leftist tree](ltree-lheap-list2.md)
- [Per-input correctness of list-to-heap construction](lheap-list2-correct.md)
- [Accumulator characterization of tail-recursive adjacent merging](merge-adj2-eq-reverse-append.md)
