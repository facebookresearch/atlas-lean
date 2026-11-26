# Quadratic dynamic program for coding-sequence alignment with frameshift extension penalties

**Setting.** A coding sequence is a DNA word over $\{a,c,g,t\}$ whose length is a multiple of $3$, read as consecutive codons. An alignment $(A', B')$ of coding sequences $A$ (length $n$) and $B$ (length $m$) is an ordinary nucleotide alignment, with gaps inserted so that no column is gap–gap. A codon is **grouped** if its three nucleotides occupy three consecutive columns. Each codon of $A$ (and symmetrically of $B$) falls into exactly one class:

- **M (matching):** grouped and aligned with a codon of the other sequence;
- **U (unmatching):** grouped and aligned with three consecutive nucleotides of the other sequence that are not a codon, so the reading frames are shifted;
- **InDel:** grouped and aligned with three gaps;
- **FS$^-$ / FS$^+$ (frameshift codons):** grouped but aligned with only one or two nucleotides, or not grouped at all.

**Score.** M and U codons are scored with an amino-acid substitution function $s_{aa}$ applied to the translated codon pair. Each U codon also pays a frameshift *extension* cost, because it continues an existing frameshift. Each InDel codon pays a codon gap cost. Nucleotides of frameshift codons aligned to a nucleotide are scored by a nucleotide function $s_{an}$, and each frameshift codon pays a frameshift *opening* cost. The total score sums these terms over both sequences. Because the extension charge depends on whether the surrounding codons are in shifted frame, the cost of a frameshift run is not an affine function of its length. Classical affine-gap recursions therefore do not apply directly.

**Theorem.** Given coding sequences $A$ and $B$ of lengths $n$ and $m$, a maximum-score alignment under this scoring scheme can be computed in $O(nm)$ time and space.

## Expansion

The algorithm fills two $(n+1)\times(m+1)$ tables indexed by prefix pairs. $D(i,j)$ is the best score of an alignment of $A[1..i]$ with $B[1..j]$, and $D_F(i,j)$ is the best score among alignments that end inside a frameshift, so that a following shifted codon can be charged the extension cost rather than the opening cost. The recurrence for each cell branches on the residues $i \bmod 3$ and $j \bmod 3$, which locate the positions inside the current codons. In each case it takes a maximum over a constant number of predecessors at distance at most $3$ in each coordinate, each with its codon or nucleotide score and opening or extension cost. Every cell is computed in constant time from earlier cells, which gives the quadratic bound, and traceback recovers the alignment. The method generalizes constant-frameshift-penalty coding alignment in the same way that Gotoh's affine gaps generalize linear gaps in the Needleman–Wunsch algorithm.

## Sources

- F. Bélanger and A. Ouangraoua, "Alignment of protein-coding sequences with frameshift extension penalties", arXiv:1508.04783 (2015), Section 2 (codon classes and alignment score) and Section 3 (dynamic-programming tables, filling lemmas and complexity theorem), <https://doi.org/10.48550/arXiv.1508.04783>.
