# Skolem sets and universal Skolem sets

Let $\mathcal{L}$ be a class of integer linear recurrence sequences. An infinite set $S \subseteq \mathbb{N}$ is a Skolem set for
$\mathcal{L}$ if there is an effective procedure that, given a sequence $\langle u_n \rangle$ in $\mathcal{L}$, decides whether
$u_n = 0$ for some $n \in S$. A universal Skolem set is a Skolem set for the class of all integer linear recurrence sequences.
By definition, the Skolem problem is decidable if and only if $\mathbb{N}$ is a universal Skolem set.

## Expansion

This node states a precise definition. A good expansion adds separate pages for the following cited results, each with its
own locator:

1. decidability of the Skolem problem already follows from the existence of a universal Skolem set that contains an infinite
   arithmetic progression;
2. with $f(n) = \lfloor \sqrt{\log n} \rfloor$ for $n \ge 1$, $s_0 = 1$ and $s_n = n! + s_{f(n)}$ for $n > 0$, the set
   $\{s_n : n \in \mathbb{N}\}$ is a universal Skolem set, of density zero (Luca, Ouaknine and Worrell, 2021, as stated in
   Section 1 of the 2022 paper);
3. there is a Skolem set of positive lower density for the class of simple linear recurrence sequences (Luca, Ouaknine and
   Worrell, 2022, Proposition 4 and Theorem 7).

## Depends on

- [Skolem, positivity and bounded reachability problems for LRS](../skolem-positivity-and-bounded-reachability-problems-for-lrs.md)

## Related topics

- [The Skolem problem](the-skolem-problem.md)

## Sources

- F. Luca, J. Ouaknine and J. Worrell, *A universal Skolem set of positive lower density*, MFCS 2022, LIPIcs 241, 73:1–73:12,
  doi:10.4230/LIPIcs.MFCS.2022.73, Definition 2 and the surrounding discussion of universal Skolem sets in Section 1;
  Proposition 4 and Theorem 7 (numbering as in the linked author copy).
  <https://people.mpi-sws.org/~joel/publications/thick_universal_skolem_set22.pdf>
- F. Luca, J. Ouaknine and J. Worrell, *Universal Skolem sets*, LICS 2021, doi:10.1109/LICS52264.2021.9470513, attributed
  through Section 1 of the MFCS 2022 paper.
