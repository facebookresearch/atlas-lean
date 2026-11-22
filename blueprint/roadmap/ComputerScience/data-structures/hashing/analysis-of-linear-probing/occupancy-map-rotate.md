# Linear probing commutes with rotations of the table

Rotate every hash address of a sequence by $j$ cells, $a_i \mapsto a_i + j \bmod N$. Then the
[occupied cells](occupancy.md) after linear probing are those of the original sequence rotated by
$j$ cells. Linear probing treats all cells of the cyclic table alike; this is the "circular
symmetry" on which Knuth's 1963 proof of Lemma 1 and the 1998 analysis of linear probing rest.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 2, proof of Lemma 1: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
- D. E. Knuth, "Linear probing and graphs", *Algorithmica* 22 (1998) 561–568, Section 1;
  arXiv:cs/9801103.
