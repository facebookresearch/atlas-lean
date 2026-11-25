# Signed reversal distance: the Hannenhalli–Pevzner formula and polynomial-time sorting

The decision problem of sorting unsigned permutations by reversals and its NP-hardness are a separate statement and are
not restated here. This node collects the signed case.

## Expansion

A sound expansion has separate pages for:

1. **Signed reversal distance** (Hannenhalli and Pevzner): the reversal distance of a signed permutation $\pi$ of
   $\{1, \dots, n\}$ to the signed identity is $d(\pi) = b(\pi) - c(\pi) + h(\pi) + f(\pi)$, with $b$ the number of breakpoints of the unsigned permutation of
   $\{1, \dots, 2n\}$ that encodes $\pi$, $c$ the number of alternating cycles of the breakpoint graph, $h$ the number of hurdles and $f(\pi) = 1$ exactly when $\pi$ is a fortress, with
   the conventions for signed permutations stated.
2. **Algorithm:** a minimum sequence of reversals for a signed permutation is computable in polynomial time
   ($O(n^4)$ in the original algorithm).

## Sources

- Algorithms for Molecular Biology lecture 11 notes: An Algorithm for Sorting Signed Permutations by Reversals - Introduction — R. Shamir, Tel Aviv University (scribe notes, 1998), Introduction: Hannenhalli and Pevzner polynomial, O(n^4); Berman-Hannenhalli faster. <https://www.cs.tau.ac.il/~rshamir/algmb/98/scribe/html/lec11/node8.html>; definitions of $b$ and $c$ <https://www.cs.tau.ac.il/~rshamir/algmb/98/scribe/html/lec11/node11.html> and Theorem 11.12 (after Hannenhalli and Pevzner) <https://www.cs.tau.ac.il/~rshamir/algmb/98/scribe/html/lec11/node13.html>.
- NP-completeness of sorting unsigned permutations by reversals — T. A. de Lima, M. Ayala-Rincon, Universidade de Brasilia technical note (2013), Abstract: Caprara showed MIN-SBR NP-hard. <https://mat.unb.br/ayala/reversals_np.pdf>
