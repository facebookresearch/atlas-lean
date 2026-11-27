# Kasai's algorithm runs in linear time

Let $\alpha$ be a type with decidable equality, $s$ a list of length $n$ over $\alpha$, and $sa$ any
permutation of $0, 1, \dots, n - 1$. Then [Kasai's algorithm](kasai.md) on $s$ and $sa$ has cost at
most $4n$, where the cost counts one unit for each position visited and one unit for each symbol
comparison.

## Remarks

- For a linearly ordered $\alpha$, the [suffix array](suffix-array.md) of $s$ is such a
  permutation, and given it the algorithm returns the [LCP array](lcp-array.md) of $s$
  ([Kasai's algorithm computes the LCP array](kasai-suffix-array.md)). So the LCP array of a list
  of length $n$ can be computed from its suffix array at cost at most $4n$.
- Finding the rank of a position in $sa$, indexing, arithmetic and building lists are not counted;
  cp-algorithms tabulates the ranks in one pass over the suffix array before the main loop.
- The bound does not use the order of the suffixes, so it holds for every permutation $sa$; the
  result is the LCP array only for the suffix array.

## Proof sketch

When the algorithm reaches position $i$, its carried length $k$ is at most $n - i$: it is one less
than a common-prefix length of the suffix starting at $i - 1$, which has $n - i + 1$ symbols, or
$0$. A position with a successor in $sa$ makes at most $\ell + 1$ comparisons, where $\ell$ is the
number of matched symbols, and its new carried length is at least $k + \ell - 1$; so its comparisons
are at most $2$ plus the increase of the carried length. Only the last entry of $sa$ has no
successor; it makes no comparison and resets the carried length, losing at most $n$. The carried
length starts and ends at $0$, so the comparisons number at most $2(n - 1) + n$, and the visits $n$.

## Comparison with the source

cp-algorithms compares each suffix with the next one in suffix-array order, as here, and states
that the algorithm runs in $O(n)$ time, because the carried length decreases at most once per
position and never exceeds $n - 1$. Demaine's notes (Section 4.1) state that the LCP array can be
constructed in $O(|T|)$ time and credit the result to Kasai et al. The sources give no explicit
constant; $4n$ is the bound of the argument above.

## Sources

- cp-algorithms, "Suffix array", <https://cp-algorithms.com/string/suffix-array.html>: section
  "Longest common prefix of two substrings without additional memory", with Kasai's algorithm and
  its $O(n)$ running-time argument.
- E. Demaine, *6.851: Advanced Data Structures*, Lecture 16 "Strings" (scribe notes, Spring 2012,
  revised 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec16.pdf>: Section 4.1,
  the LCP array in $O(|T|)$ time (Kasai et al.), with the example text `banana$`, whose suffix
  array is $[6, 5, 3, 1, 0, 4, 2]$ and LCP array $[0, 1, 3, 0, 0, 2]$.
