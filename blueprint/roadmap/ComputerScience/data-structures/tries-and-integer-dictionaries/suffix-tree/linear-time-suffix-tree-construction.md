# Suffix trees in linear time through suffix arrays

Let $T$ be a text over a linearly ordered alphabet $\Sigma$ whose last letter occurs nowhere else
in $T$ and is smaller than every other letter, and let $\mathrm{sort}(\Sigma)$ be the time needed
to sort the letters of $T$. Then the suffix tree of $T$, the compacted trie of its suffixes, can be
built in $O(|T| + \mathrm{sort}(\Sigma))$ time on a
[word RAM](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md),
which is $O(|T|)$ when the letters are integers in $\{0, 1, \dots, |T|\}$.

## Proof sketch

The DC3 algorithm computes the suffix array of $T$ in $O(|T| + \mathrm{sort}(\Sigma))$ time.
Kasai's algorithm then computes the LCP array from the suffix array with at most $4|T|$ position
visits and letter comparisons. On the word RAM, with $T$ and the suffix array stored in arrays, the
inverse array of the suffix array computed in one pass beforehand, and each LCP entry written
directly into an array, each visit and each comparison takes constant time, so this step takes
$O(|T|)$ time. The Cartesian tree of the LCP array, with the suffix-array entries inserted as
leaves, gives the suffix tree in $O(|T|)$ time. Integers in $\{0, 1, \dots, |T|\}$ are sorted in
$O(|T|)$ time by counting sort.

## Depends on

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Suffix-array construction by the DC3 algorithm](../suffix-array/dc3-suffix-array-construction.md)
- [Kasai's algorithm computes the LCP array](../suffix-array/kasai-suffix-array.md)
- [Kasai's algorithm runs in linear time](../suffix-array/construction-time-of-suffix-arrays-lcp-arrays-and-suffix-trees.md)
- [Suffix tree from the suffix array and the LCP array](suffix-tree-from-suffix-and-lcp-arrays.md)
- [Running time of counting sort](../../../sorting-and-searching/counting-sort/counting-sort-time.md)

## Background

- [Suffix tree](suffix-tree.md): the suffix tree as a radix trie over `Option α`, with a fresh
  terminator `none`.

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 16 "Strings" (scribe notes, Spring 2012,
  revised 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec16.pdf>: Section 5,
  which derives linear-time suffix-tree construction from the DC3 algorithm and the linear-time
  passage from suffix arrays to suffix trees of Section 4.2.2, and notes that Farach, McCreight,
  Ukkonen and Weiner proved it independently of DC3; Section 4.1, the LCP array in $O(|T|)$ time.
