# Number of hash sequences without overflow

Let $0 < k \le n$. The number of hash sequences $f : \{0, \dots, k-1\} \to \{0, \dots, n-1\}$ for
which linear probing without wrap-around places all $k$ items in a table of $n$ cells
([without overflow](../../../../Combinatorics/parking-functions/lin-success.md)) is

$$(n + 1 - k)(n + 1)^{k - 1}.$$

This is Lemma 1 of Knuth's 1963 note, which writes the count as $(n+1)^k - k(n+1)^{k-1}$. His lemma holds for $0 \le k \le n + 1$; the cases $k = 0$ (one
sequence) and $k = n + 1$ (none) are left out here. For $k = n$ the count
$(n+1)^{n-1}$ is the number of parking functions of length $n$.

Knuth's proof is the circle argument: run the cyclic algorithm on $n + 1$ cells; by rotational
symmetry each cell is left empty by exactly a fraction $(n + 1 - k)/(n + 1)$ of the $(n+1)^k$
sequences, and the sequences leaving the last cell empty are exactly the non-overflow sequences on
$n$ cells. Equivalently, non-overflow sequences are exactly the partial parking functions, and
[Pollak's count of partial parking functions](../../../../Combinatorics/parking-functions/pollak-partial-parking-functions-card.md), proved by the same circle argument, gives the
formula. In the cyclic model of this topic the circle argument is
[rotational symmetry of linear probing](mul-card-not-mem-occupancy.md) and the
[number of sequences that leave a given cell empty](card-not-mem-occupancy.md).

## Informally uses

- [Number of hash sequences that leave a given cell empty](card-not-mem-occupancy.md): the
  circle argument on $n + 1$ cells, the step of Knuth's proof.

## Background

- [Linear probing succeeds exactly on partial parking functions](../../../../Combinatorics/parking-functions/lin-success-iff-is-partial-parking-funct.md):
  the identification behind the equivalent count.
- [Number of partial parking functions](../../../../Combinatorics/parking-functions/pollak-partial-parking-functions-card.md):
  the count that this identification transfers.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 2, Lemma 1: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
