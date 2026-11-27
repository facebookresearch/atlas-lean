# Hodge Fibre Identification

The fibres over λ of the Hodge moduli spaces are the fixed-parameter moduli spaces. Let $X$ be
an integral, Noetherian, proper and projective complex variety, smooth of dimension $d$, with a
complex point $x$ and an ample line bundle $H$, and let $n > 0$. Families over a complex scheme $S$
are framed rank-$n$ relative λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`)
is taken for the given pullback system with its coherence, unit-fibre comparison and fibre tests,
and the given dualizing complexes, proper pullbacks and characteristic class theory. Assume
admissibility stable under reindexing and under change of frame and scaling (`ReindexingProofs`,
`ActionAdmissibility`), and fix the given frame structures on $\mathrm{GL}_n$ and $\mathrm{GL}_1$
and scaling action of $\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`, `ScalingParameterTheory`).
Given the framed and coarse Hodge moduli spaces $R \to M$ (`HodgeRepresentation`, `HodgeQuotient`)
and, for $\lambda \in \mathbb{C}$, fixed-parameter spaces $R_\lambda \to M_\lambda$
(`FixedRepresentation`, `FixedQuotient`), there are isomorphisms from the fibre of $R$ over
$\lambda \in \mathbb{A}^1$ to $R_\lambda$ and from the fibre of $M$ over λ to $M_\lambda$ that
identify the family classes represented by maps to the fibre of $R$ with those represented by
$R_\lambda$, and that commute with the quotient maps (`FibreIdentification`).
