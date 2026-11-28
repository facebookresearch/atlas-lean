# Suffix tree from the suffix array and the LCP array

Let $T$ be a text whose last letter occurs nowhere else in $T$ and is smaller than every other
letter. Given the [suffix array](../suffix-array/suffix-array.md) and the
[LCP array](../suffix-array/lcp-array.md) of $T$, the suffix tree of $T$, that is, the compacted
trie of the suffixes of $T$ with the children of each node ordered by the first letters of their
edges, can be built with the letter depth of each internal node in $O(|T|)$ time on a
[word RAM](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md).
Its internal nodes form the [Cartesian tree](../../search-trees/cartesian-tree/build.md) of the
LCP array in which each node holds all the minima of its range rather than one, the letter depth
of an internal node is the LCP value it holds, and its leaves are the entries of the suffix array,
in order.

## Proof sketch

The suffix array lists the leaves of the suffix tree in the order of an in-order walk, and the LCP
value between two consecutive leaves is the letter depth of their lowest common ancestor. The
smallest LCP values, all of them, belong to the root; the entries between two of them, and those
before the first and after the last, belong to its subtrees, built in the same way. So the
Cartesian tree of the LCP array with all minima of a range at one node has the internal nodes of
the suffix tree, with their letter depths, and inserting the suffix-array entries in order as
leaves gives the suffix tree. Such a Cartesian tree is built in linear time.

## Depends on

- [Suffix array](../suffix-array/suffix-array.md)
- [The LCP array](../suffix-array/lcp-array.md)
- [Cartesian tree of a list](../../search-trees/cartesian-tree/build.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Background

- [Suffix tree](suffix-tree.md): the suffix tree as a radix trie over `Option α`, with a fresh
  terminator `none`.

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 16 "Strings" (scribe notes, Spring 2012,
  revised 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec16.pdf>: Section 4.2
  and Figures 2 and 3, the suffix array as the leaves and the LCP array as the letter depths of
  the internal nodes, and Section 4.2.2, the suffix tree as the Cartesian tree of the LCP array
  with all minima at the root, built in linear time (by the Cartesian-tree construction of
  Lecture 15).
