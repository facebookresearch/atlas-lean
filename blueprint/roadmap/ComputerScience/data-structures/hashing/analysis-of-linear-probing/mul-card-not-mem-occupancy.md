# Rotational symmetry of linear probing

Let $n \le N$ and let $c$ be a cell of a cyclic table of $N$ cells. Then

$$N \cdot \#\{a \in \{0, \dots, N-1\}^n : \text{linear probing with } a \text{ leaves } c
\text{ empty}\} = (N - n)\, N^n .$$

[Rotating the hash addresses](occupancy-map-rotate.md) is a bijection between the sequences that
leave $c$ empty and those that leave any other cell empty, so every cell is left empty by the same
number of sequences. Each sequence leaves exactly $N - n$ cells empty, since its
[$n$ items occupy $n$ cells](card-occupancy.md). Summing over the $N$ cells gives the identity.
This is the circle argument of Knuth's 1963 proof of Lemma 1 and of Section 1 of his 1998 paper.

## Informally uses

- [Linear probing commutes with rotations of the table](occupancy-map-rotate.md): the bijection
  between cells.
- [Linear probing places every item while the table has room](card-occupancy.md): every sequence
  leaves $N - n$ cells empty.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 2, proof of Lemma 1: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
- D. E. Knuth, "Linear probing and graphs", *Algorithmica* 22 (1998) 561–568, Section 1;
  arXiv:cs/9801103.
