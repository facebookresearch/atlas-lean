# Polynomial-time sorting of signed permutations by reversals

Given a signed permutation $\pi$ of $\{1, \dots, n\}$, a minimum sequence of signed
reversals sorting $\pi$ to the signed identity can be computed in polynomial time
($O(n^4)$ in the original Hannenhalli–Pevzner algorithm).

## Depends on

- [Signed permutation of 1, …, n](../../../../Combinatorics/permutations/permutation-statistics/sorting-by-reversals/svalid.md)
- [Signed reversal of the block of positions i to j of a list](../../../../Combinatorics/permutations/permutation-statistics/sorting-by-reversals/srev-block.md)
- [Signed reversal distance of a signed permutation](../../../../Combinatorics/permutations/permutation-statistics/sorting-by-reversals/sdist.md)

## Proof depends on

- [Hannenhalli–Pevzner signed reversal distance formula](sdist-eq.md)

## Expansion

A sound expansion has separate pages for:

1. **The sorting procedure** (algorithm Reversal_Sort, Section 8). While $\pi$ is not sorted: on a
   long cycle of the breakpoint graph apply a safe $(g, b)$-padding (Theorem 2); otherwise, in an
   oriented component apply a safe reversal (Theorem 4); otherwise, with an even number of hurdles
   apply a safe reversal merging two hurdles (Lemmas 18 and 19); otherwise, with a simple hurdle
   apply a safe reversal cutting it (Lemmas 15 and 19); otherwise, in a fortress with more than
   three superhurdles apply a safe reversal merging two superhurdles (Lemma 18); otherwise, in a
   3-fortress, apply a reversal merging two superhurdles. The generalized sorting so obtained, by
   reversals and paddings, is then mimicked by a genuine sorting of $\pi$ (Lemma 9).
2. **Optimality** (Theorem 6, from Theorem 5 and Lemma 9). The generalized sorting contains
   exactly $d(\pi) = b(\pi) - c(\pi) + h(\pi) + f(\pi)$ reversals, and the genuine sorting that
   mimics it uses $d(\pi)$ reversals.
3. **Operation count behind the $O(n^4)$ bound** (proof of Theorem 6). Each iteration decreases the
   quantity $\mathrm{complexity}(\pi) + 3d(\pi)$ of the source by at least one, so there are at most
   $4n$ iterations, and the most expensive iteration, the search for a safe reversal in an
   oriented component, takes $O(n^3)$ time on simple permutations.

## Sources

- S. Hannenhalli and P. A. Pevzner, Transforming cabbage into turnip: polynomial algorithm
  for sorting signed permutations by reversals, J. ACM 46 (1999), 1–27, Section 8 (algorithm
  Reversal_Sort and Theorem 6), Theorems 2, 4 and 5, Lemmas 9, 15, 18 and 19.
- Algorithms for Molecular Biology lecture 11 notes: An Algorithm for Sorting Signed
  Permutations by Reversals - Introduction — R. Shamir, Tel Aviv University (scribe notes,
  1998). <https://www.cs.tau.ac.il/~rshamir/algmb/98/scribe/html/lec11/node8.html>
