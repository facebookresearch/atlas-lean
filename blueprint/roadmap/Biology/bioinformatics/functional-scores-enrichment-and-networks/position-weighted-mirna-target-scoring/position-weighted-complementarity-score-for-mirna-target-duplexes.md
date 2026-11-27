# Position-weighted complementarity score for miRNA-target duplexes

Let a mature microRNA $m = m_1 m_2 \cdots m_L$ be indexed from its $5'$ end and let $u$ be a candidate target sequence (a $3'$ untranslated region). A *duplex alignment* $A$ is a local alignment of $m$ against the reverse complement orientation of $u$, that is an antiparallel double-stranded pairing, with gaps allowed in either strand. Score an aligned residue pair involving position $p$ of the microRNA by

$$\sigma(p, \text{pair}) = w_p \cdot \begin{cases} +5, & \text{Watson-Crick pair (G:C or A:U)},\\ +2, & \text{G:U wobble pair},\\ -3, & \text{mismatch},\end{cases} \qquad w_p = \begin{cases} 2, & 1 \le p \le 11,\\ 1, & p > 11,\end{cases}$$

and charge affine gap costs with opening $-8$ and elongation $-2$. The alignment score is

$$S(A) = \sum_{(p,q) \in A_{\mathrm{pairs}}} \sigma(p, \text{pair}(p,q)) \; - \; \sum_{\text{gap runs } r} \bigl(8 + 2(\lvert r \rvert - 1)\bigr),$$

and the site score is $S = \max_A S(A)$, computed by dynamic programming over local alignments. Let $\Delta G$ be the free energy of formation of the duplex of the aligned segments from the completely dissociated state. A position of $u$ is a *candidate target site* when

$$S > 90 \quad \text{and} \quad \Delta G < -17 \ \mathrm{kcal/mol}.$$

Candidate sites are retained as predicted targets only if they are conserved: the site must occur in the aligned untranslated regions of orthologous genes at positions differing by at most $10$ residues, with sequence identity at least $90\%$ between human and mouse or rat, and at least $70\%$ between the two fish genomes compared. Sites are ranked by $S$, with $\Delta G$ as secondary key, and among microRNAs hitting the same site (or within $25$ nucleotides of it) only the highest-scoring, lowest-energy one is reported.

## Depends on

- [The table computes the optimal local alignment score](../../sequence-alignment/smith-waterman-local-alignment/sw-tab-eq-local-score.md)
- [Affine-gap alignment score](../../sequence-alignment/gotoh-affine-gap-alignment/affine-score.md)

## Remarks

The scheme is ordinary local alignment with two biological modifications. The weight $w_p$ encodes the experimentally observed $5'$-$3'$ asymmetry of microRNA pairing: within the first eleven positions a Watson-Crick pair contributes $+10$ rather than $+5$, so a seed-proximal match is worth twice a distal one, and the threshold $S > 90$ cannot be reached by distal pairing alone. The intermediate reward $+2$ for a G:U wobble, below a Watson-Crick pair but above a mismatch, reflects that wobbles are tolerated yet penalized relative to standard thermodynamics, and they are rarer in the weighted $5'$ region.

Score and free energy are complementary filters rather than redundant ones: $S$ measures weighted complementarity with positional structure, while $\Delta G$ measures the thermodynamic stability of the resulting duplex, including loop and stacking contributions that a position-additive score cannot express. Requiring both removes high-scoring alignments that would not form a stable duplex.

The conservation requirement supplies the statistical control. The two thresholds alone produce many hits in any long untranslated region, since score grows with sequence length; demanding that the same site survives in an orthologous region at a matching position, within a tolerance of $\pm 10$ aligned residues, makes a chance hit implausible. The false positive level of the whole procedure is estimated by rerunning it on microRNA sequences randomized by repeated transposition of pairs of bases, keeping base composition fixed.

## Sources

- B. John, A. J. Enright, A. Aravin, T. Tuschl, C. Sander, D. S. Marks, "Human MicroRNA targets", PLoS Biology 2(11) (2004) e363, Materials and Methods, "miRNA target prediction", <https://doi.org/10.1371/journal.pbio.0020363> (PMC521178).
