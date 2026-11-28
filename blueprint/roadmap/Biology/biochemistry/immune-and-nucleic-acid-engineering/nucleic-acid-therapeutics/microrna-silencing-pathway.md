# MicroRNA silencing and the mimic/antagomiR pair

A microRNA guides a protein complex to partially complementary sites in target transcripts and represses them. Two therapeutic modalities follow: a *mimic* supplies a microRNA whose level is low, and an *antagomiR* is an antisense oligonucleotide that inhibits the activity of a mature microRNA whose level is high.

Terms and their limits:

- *Mimic*: a mature microRNA duplex with the sequence of the endogenous species, intended to restore its activity.
- *AntagomiR*: a single-stranded synthetic RNA complementary to a mature microRNA, used to inhibit that microRNA's activity. The detailed mechanism of inhibition is not established by the sources read here and is not asserted.
- *OncomiR*: a microRNA whose elevated level is associated with progression in a stated tumor type; the label is context-dependent and never a property of a sequence alone.
- *Specificity.* Pairing to the seed region, nucleotides 2-7 of the mature microRNA, is a major determinant of target recognition; a match to nucleotide 8 augments the seed match rather than belonging to the seed itself, giving the site type named for that augmentation. Seed pairing is not the only determinant: site context features also shape efficacy, and seed matches are reported not always to be sufficient for repression. Whether a single mismatch in a seed-complementary site abolishes regulation is a question about one site and transcript; the case studied in this field is given in [A polymorphism inside a microRNA binding site switches regulation on and off](./seed-site-polymorphism-and-microrna-targeting.md).
- *Processing and effector machinery.* Dicer participates in upstream RNA processing; Argonaute is the central effector of the RNA-induced silencing complex. In the triplex study of [RNA triple-helix construct for co-delivery of two microRNA cargos](./rna-triple-helix-delivery-construct.md), recombinant Dicer and AGO2 were both tested, and cleavage of the assembled construct into smaller products was reported only with AGO2 under those conditions. That is one assay, not a general account of processing.

## Context

Undergraduate level. This vocabulary and the pairing page are parallel foundations: the construct page needs both, but silencing can be understood without triplex chemistry. The relation to the construct page is direct: one construct carries a mimic and an antagomiR together, and its recognition by recombinant enzymes was tested as part of characterization.

## Depends on

None.

## Proof depends on

None.

## Expansion

A quantitative treatment would require: biogenesis kinetics; occupancy of target sites given microRNA and transcript abundances; competition among targets for shared microRNA pools; the contribution of non-seed pairing; and off-target repression. None of that follows from the definitions above.

## Sources

- J. Conde, N. Oliva, M. Atilano, H. S. Song, N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3):353-363 (2016). DOI 10.1038/nmat4497. Read: PubMed Central author manuscript PMC6594154 - Introduction (mimic and antagomiR definitions; miR-205 and miR-221 rationale in triple-negative breast cancer) and the paragraph accompanying Supplementary Figure 12, reporting recognition and cleavage only in the presence of recombinant AGO2. https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/
- A. Grimson, K. K.-H. Farh, W. K. Johnston, P. Garrett-Engele, L. P. Lim, D. P. Bartel, "MicroRNA targeting specificity in mammals: determinants beyond seed pairing", *Molecular Cell* 27(1):91-105 (2007). DOI 10.1016/j.molcel.2007.06.017. Research paper. Read: the PubMed Central author manuscript PMC3800283 - Summary (seed matches "are not always sufficient for repression"; five context features that boost site efficacy) and Introduction, paragraph on canonical site types with Figure 1A, which defines the 6mer as "the perfect 6-nt match to the miRNA seed (miRNA nucleotides 2-7)" and the 7mer-m8 site as "the seed match augmented by a match to miRNA nucleotide 8". https://pmc.ncbi.nlm.nih.gov/articles/PMC3800283/
