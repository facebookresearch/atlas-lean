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
- The bound does not use the order of the suffixes, so it holds for every permutation $sa$. The
  output is guaranteed to be the LCP array when $sa$ is the suffix array, and it can be for other
  permutations too: for `ab` and $sa = [1, 0]$ it is $[0]$, the LCP array of `ab`.
- Finding the rank of a position in $sa$, indexing, arithmetic and building lists are not counted.
  On a word RAM with $s$ and $sa$ stored in arrays, as in cp-algorithms, the inverse array of $sa$
  is tabulated in one pass before the main loop and each recorded value is written directly into
  the output array; each visit and each comparison then takes constant time, and the algorithm runs
  in $O(n)$ time.
- Given the suffix array in reverse order, the algorithm compares each suffix with its predecessor
  in suffix-array order instead, and the bound $4n$ holds for that order too.
  [Kasai et al.: the LCP array in linear time](../../../string-algorithms/palindromes-lcp-arrays-and-multipattern-matching/kasai-linear-time-lcp.md)
  states the correctness and the word-RAM bound of that predecessor variant.

## Proof sketch

If $n = 0$ the algorithm visits no position and its cost is $0$; let $n \ge 1$. By induction on $i$,
the carried length $k$ at position $i$ is at most $n - i$. It is $0$ at $i = 0$. If $i$ has a
successor $j$ in $sa$, the algorithm matches some number $\ell$ of symbols of the suffixes starting
at $i + k$ and $j + k$, with at most $\ell + 1$ comparisons, and $\ell \le n - (i + k)$, the length
of the suffix starting at $i + k$; so it records $k + \ell \le n - i$ and carries
$k' = \max(k + \ell - 1, 0) \le n - (i + 1)$. Otherwise it carries $0$. This uses only the length
of the text, not that the recorded values are common-prefix lengths, so it holds for every
permutation $sa$. The comparisons at a position with a successor number at most
$\ell + 1 \le k' - k + 2$. Exactly one position, the last entry of $sa$, has no successor; it makes
no comparison and resets the carried length to $0$, lowering it by at most $n$. The carried length
starts and ends at $0$, so the comparisons number at most $2(n - 1) + n$, and the visits $n$.

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
