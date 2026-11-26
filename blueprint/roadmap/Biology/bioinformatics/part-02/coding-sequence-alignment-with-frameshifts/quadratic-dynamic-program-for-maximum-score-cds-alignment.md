# Quadratic-time dynamic program for maximum-score CDS alignment with frameshift extension penalties

**Theorem.** Let $A$ and $B$ be coding DNA sequences of lengths $n$ and $m$, scored by the [frameshift-aware alignment score](frameshift-aware-score-of-a-coding-sequence-alignment.md) with frameshift opening and extension penalties. A maximum-score alignment of $A$ and $B$ can be computed in $O(nm)$ time and space.

**Algorithm.** Use two $(n+1)\times(m+1)$ tables:

- $D(i,j)$, the maximum score of an alignment of the prefixes $A[1..i]$ and $B[1..j]$;
- $D_F(i,j)$, filled only when $i\equiv0$ or $j\equiv0\pmod3$: $D_F(i,j)=D(i,j)$ if both are multiples of $3$; otherwise it is the maximum score of an alignment of $A[1..i+\alpha]$ with $B[1..j+\alpha]$, $\alpha=(3-i)\bmod 3$ (resp. $(3-j)\bmod3$), in which the last $\alpha$ nucleotides of the two prefixes are aligned pairwise and half of their nucleotide scores is subtracted. It records partial codons that will later be completed into frameshift-extension codons.

Initialize $D(i,0)=\lfloor i/3\rfloor\,\texttt{gap}$, $D(0,j)=\lfloor j/3\rfloor\,\texttt{gap}$ (with the matching $D_F$ boundary values), then fill both tables in increasing $(i,j)$, computing $D(i,j)$ by a constant number of cases that depend on $(i\bmod3,j\bmod3)$ (Lemma 1 of the source; for $i\equiv j\equiv0$ these include an in-frame codon match $s_{aa}(A[i-2..i],B[j-2..j])+D(i-3,j-3)$ and several frameshift-opening moves costing $2\,\texttt{fs\_open}$), and then $D_F(i,j)$ by the cases of Lemma 2. Backtracking from $D(n,m)$ recovers an optimal alignment.

## Expansion

Correctness is a case analysis on how the last columns of an optimal prefix alignment can end, for each residue pattern of $(i,j)$ modulo $3$: an in-frame codon pair, an indel codon, a codon broken by a frameshift, or the completion of a frameshift-extension codon, the last of which needs the auxiliary table $D_F$ because the two codons involved end at different alignment positions. Each of the $2(n+1)(m+1)$ cells is filled in constant time; counting the cases gives about $12.55\,nm$ elementary operations. The method keeps the quadratic cost of Needleman–Wunsch while scoring alignments at the amino-acid level and penalizing the length of frameshift translations.

## Depends on

- [Frameshift-aware score of a coding sequence alignment](frameshift-aware-score-of-a-coding-sequence-alignment.md)

## Sources

- S. Jammali, E. Kuitche, A. Rachati, F. Bélanger, M. Scott and A. Ouangraoua, "Aligning coding sequences with frameshift extension penalties", Algorithms for Molecular Biology 12 (2017), article 10, sections "Preliminaries: Score of CDS alignment" and "Method": Definitions 1–4, Lemmas 1–2 and Theorem 1, <https://doi.org/10.1186/s13015-017-0101-4>; preprint arXiv:1610.08809, <https://doi.org/10.48550/arXiv.1610.08809>.
