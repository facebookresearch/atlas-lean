# Construction time of suffix arrays, LCP arrays and suffix trees

Let $T$ be a string of length $n$ over an alphabet of integers in $\{0, \dots, n\}$, terminated by a unique smallest symbol. The [suffix array](suffix-array.md) of $T$ lists the start positions of its suffixes in lexicographic order. The [LCP array](lcp-array.md) records the length of the longest common prefix of each pair of adjacent suffixes in that order.

**Theorem.**
1. **Prefix doubling.** The suffix array can be computed in $O(n\log n)$ time.
2. **Kasai's algorithm.** Given the suffix array, the LCP array can be computed in $O(n)$ time.
3. **Suffix tree from the arrays.** Given both arrays, the suffix tree of $T$, with the string depth of every internal node, can be built in $O(n)$ time. Its internal nodes form the Cartesian tree of the LCP array, with all minima merged at each root, and its leaves are the suffix-array entries in order.
4. Together with linear-time suffix array construction, for example by the DC3 algorithm in $O(n + \mathrm{sort}(\Sigma))$ time, suffix trees can be built in linear time.

**Proof.**
1. In round $k = 0, 1, \dots, \lceil \log_2 n \rceil$, sort the cyclic substrings of length $2^k$ and assign each one its equivalence class $c[i]$ among them. A substring of length $2^{k+1}$ starting at $i$ is determined by the pair $(c[i], c[i + 2^k])$. So each round is a radix sort of $n$ pairs of integers below $n$, done with two stable counting sorts, in $O(n)$ time.
2. Process the suffixes in order of their start position $i = 0, 1, \dots$, comparing each with its successor in the suffix array. If suffix $i$ shares $h > 0$ characters with its successor, then suffix $i + 1$ shares at least $h - 1$ characters with its own successor. So the running match length decreases by at most $1$ per step and never exceeds $n$, which bounds the total work by $O(n)$.
3. Build the Cartesian tree of the LCP array with a stack in $O(n)$ time, merging equal minima. Its node values are the string depths of the internal suffix-tree nodes. Insert the suffix-array entries as leaves in order.

## Depends on

- [Suffix array](suffix-array.md)
- [The LCP array](lcp-array.md)

## Background

- [Suffix tree](../suffix-tree/README.md)

## Sources

- cp-algorithms, "Suffix array", <https://cp-algorithms.com/string/suffix-array.html>: the $O(n\log n)$ algorithm sorting cyclic substrings of length $2^k$ by pairs of equivalence classes with counting sort, and Kasai's algorithm for the LCP array with its $O(n)$ running-time argument.
- E. Demaine, *6.851: Advanced Data Structures*, Lecture 16 "Strings" (scribe notes, Spring 2012, revised 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec16.pdf>:
    - Section 4: the LCP array in $O(|T|)$ time (Kasai et al.);
    - Section 4.2.2: the suffix tree obtained from the suffix array and LCP array through a Cartesian tree in linear time;
    - Section 5: the DC3 algorithm in $O(|T| + \mathrm{sort}(\Sigma))$ time.
