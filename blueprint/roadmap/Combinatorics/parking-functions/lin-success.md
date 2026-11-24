# Linear probing without overflow

A hash sequence $f : \{0, \dots, s - 1\} \to \{0, \dots, t - 1\}$ is *without overflow* when
linear probing without wrap-around places all $s$ items in a table of $t$ cells: item $i$ goes
into the first free cell at or after $f(i)$, and no item runs past the last cell. Equivalently,
all $s$ cars park on a one-way street of $t$ spots, car $i$ starting at spot $f(i)$.

These are the sequences that Lemma 1 of Knuth's 1963 note counts. In Knuth's cyclic algorithm on
$n$ cells, they are the sequences for which the overflow step never occurs.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Sections 1 and 2: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf

## Related topics

- [Analysis of linear probing](../../ComputerScience/data-structures/hashing/analysis-of-linear-probing/README.md):
  the number of these sequences (Knuth's Lemma 1) and the expected cost of linear probing.
