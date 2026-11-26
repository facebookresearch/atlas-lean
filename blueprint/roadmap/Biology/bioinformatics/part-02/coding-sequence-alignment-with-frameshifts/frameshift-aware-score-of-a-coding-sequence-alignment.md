# Frameshift-aware score of a coding sequence alignment

**Definitions.** A *coding DNA sequence* (CDS) is a word over $\Sigma_N=\{A,C,G,T\}$ of length $n\equiv0\pmod3$, read as $n/3$ codons ending at positions $3i$. An alignment of CDS $A,B$ is a pair $(A',B')$ of equal-length gapped copies with no all-gap column. A codon is *grouped* in the alignment if its three nucleotides occupy three consecutive columns. The codons of $A$ (and symmetrically of $B$) are partitioned into

- **IM** (in-frame matching): grouped and aligned with a codon of the other CDS;
- **FSext** (frameshift extension): grouped and aligned with three nucleotides overlapping two codons of the other CDS;
- **InDel**: grouped and aligned with three gap symbols;
- **FSinit** (frameshift initiation): all other codons; their nucleotides aligned with a nucleotide of the other CDS form the set **MFS**.

Codons and nucleotides are identified by the alignment column of their last nucleotide, so $\mathrm{IM}_{A\to B}=\mathrm{IM}_{B\to A}$.

**Score.** Given a symmetric amino-acid substitution score $s_{aa}$ on codons (via translation, so synonymous codons score as identical), a symmetric nucleotide score $s_{an}$, and negative costs $\texttt{gap}$, $\texttt{fs\_open}$, $\texttt{fs\_extend}$, the score of $(A',B')$ is

$$
\begin{aligned}
\mathrm{score}(A',B')=&\sum_{k\in\mathrm{IM}_{A\to B}}s_{aa}\big(A'[k-2..k],B'[k-2..k]\big)\\
&+\sum_{X\to Y}\Big[\sum_{k\in\mathrm{FSext}_{X\to Y}}\Big(\tfrac12 s_{aa}\big(X'[k-2..k],Y'[k-2..k]\big)+\texttt{fs\_extend}\Big)+|\mathrm{InDel}_{X\to Y}|\,\texttt{gap}\\
&\qquad+\Big(\tfrac{|X|}{3}-|\mathrm{IM}_{X\to Y}|-|\mathrm{FSext}_{X\to Y}|-|\mathrm{InDel}_{X\to Y}|\Big)\texttt{fs\_open}+\sum_{k\in\mathrm{MFS}_{X\to Y}}\tfrac12 s_{an}\big(X'[k],Y'[k]\big)\Big],
\end{aligned}
$$

where the outer sum runs over the two directions $A\to B$ and $B\to A$.

## Expansion

Classical frameshift-aware aligners penalize only the opening of a frameshift, so a long stretch translated in a shifted frame costs the same as a short one. This score charges every codon translated in a shifted frame (an FSext codon) a fixed extension cost while still scoring its amino-acid similarity at half weight per direction, and charges each codon broken by a frameshift an opening cost, so the alignment can distinguish a genuine short frameshift from a spurious long one. In-frame matches are counted once (both directions coincide), while frameshifted material is scored from each sequence's own reading frame, hence the factors $\tfrac12$.

## Sources

- S. Jammali, E. Kuitche, A. Rachati, F. Bélanger, M. Scott and A. Ouangraoua, "Aligning coding sequences with frameshift extension penalties", Algorithms for Molecular Biology 12 (2017), article 10, sections "Preliminaries: Score of CDS alignment" and "Method": Definitions 1–4, Lemmas 1–2 and Theorem 1, <https://doi.org/10.1186/s13015-017-0101-4>; preprint arXiv:1610.08809, <https://doi.org/10.48550/arXiv.1610.08809>.
