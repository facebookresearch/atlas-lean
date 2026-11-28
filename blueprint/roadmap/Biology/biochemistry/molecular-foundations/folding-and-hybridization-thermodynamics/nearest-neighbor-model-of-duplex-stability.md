# Nearest-neighbor model of DNA duplex stability

In the nearest-neighbor model variant adopted here, the standard free energy of forming a Watson–Crick DNA duplex is predicted as a sum of empirical stacking terms for its adjacent base-pair doublets, one initiation term per duplex end according to the terminal pair, and a symmetry term for self-complementary duplexes; enthalpy and entropy are summed the same way.

**Model.** A duplex of $n\ge2$ base pairs is written as a top strand $5'\to3'$ paired antiparallel with its Watson–Crick complement. Each pair of adjacent base pairs is one of the ten distinct nearest-neighbor (NN) doublets $AA/TT$, $AT/TA$, $TA/AT$, $CA/GT$, $GT/CA$, $CT/GA$, $GA/CT$, $CG/GC$, $GC/CG$, $GG/CC$ (a doublet and its reverse complement are the same doublet). Let $n_i$ be the number of occurrences of doublet $i$ ($\sum_in_i=n-1$), and let $m_{GC},m_{AT}\in\{0,1,2\}$ with $m_{GC}+m_{AT}=2$ count the duplex ends whose terminal base pair is G·C or A·T. The strand is **self-complementary** if it equals its own reverse complement (so the duplex is formed from two identical strands). The model is

$$\Delta G^\circ_{37}=m_{GC}\,g_{GC}+m_{AT}\,g_{AT}+\sum_{i=1}^{10}n_i\,\Delta G^\circ_{37}(i)+\Delta G^\circ_{37}(\mathrm{sym}),$$

where $g_{GC},g_{AT}$ are the initiation parameters "with terminal G·C" and "with terminal A·T", and the symmetry term is applied once per duplex: for a self-complementary duplex $\Delta H^\circ(\mathrm{sym})=0$ and $\Delta S^\circ(\mathrm{sym})=-1.4$ cal mol$^{-1}$K$^{-1}$, so $\Delta G^\circ_{37}(\mathrm{sym})=+0.43$ kcal/mol; otherwise all three are $0$. $\Delta H^\circ$ and $\Delta S^\circ$ are summed with the same multiplicities from the enthalpy and entropy tables, and at any temperature $T$ in kelvin $\Delta G^\circ_T=\Delta H^\circ-T\Delta S^\circ$ (an identity; using tabulated $\Delta H^\circ,\Delta S^\circ$ far from 37 °C additionally assumes no heat-capacity change).

**Counting convention and status.** The one-term-per-end reading of the initiation parameters ($m_{GC}+m_{AT}=2$, so two terms of the same kind when both ends share a class) is the convention adopted here; the source's worked example has one end of each kind and uses each term once, which is consistent with it, but the source's Table 1 defers the exact format to its ref. 22, which was not read. The parameters are empirical fits to melting data referred to 1 M NaCl (the oligomer and polymer data sets were fitted separately and should not be interchanged), salt corrections are outside this page, and use of the model for a given duplex assumes two-state melting. Predictions are empirical estimates, not theorems.

## Context

Undergraduate to graduate biochemistry. NN parameters are the basis of melting-temperature and hybridization-energy prediction for primers, probes, antisense and RNA-interference strands, and, with RNA parameters, of secondary-structure energy models such as the [additive energy of the McCaskill partition function](../../../bioinformatics/mccaskill-partition-function-for-rna-folding/energy.md). The Artzi laboratory's RNA-triple-helix nanoparticles are assembled from designed complementary strands whose duplex and triplex stabilities were assessed by melting (Conde et al. 2016); this DNA model is a foundation for such design but is not the RNA or triplex energy model those strands require.

## Depends on

None.

## Proof depends on

None.

## Expansion

Worked check: for the source's example $5'$-CGTTGA-$3'$ paired with its complement (ends C·G and A·T, so $m_{GC}=m_{AT}=1$; doublets CG/GC, GT/CA, TT/AA$=$AA/TT, TG/AC$=$CA/GT, GA/CT; not self-complementary), the unified $\Delta G^\circ_{37}$ values sum to $-7.36$ kcal/mol for the stacks and $+0.98+1.03$ for initiation, giving $-5.35$ kcal/mol as in the source's Fig. 1.

Remaining decomposition before the page can be marked ready: (i) a source that states the initiation counting rule in text (the 1998 paper's ref. 22 or a later unified review) to confirm the per-end convention; (ii) definition pages for the doublet-count map from sequences to $\mathbb N^{10}$ and for self-complementarity; (iii) separate model pages for salt corrections and for RNA and triplex parameters. The identifiability of the ten doublet parameters from melting data is the subject of [rank deficiency of the nearest-neighbor stacking matrix](rank-deficiency-of-the-nearest-neighbor-stacking-matrix.md).

## Sources

- J. SantaLucia Jr., "A unified view of polymer, dumbbell, and oligonucleotide DNA nearest-neighbor thermodynamics", *Proceedings of the National Academy of Sciences USA* 95(4) (1998), 1460–1465, [doi.org](https://doi.org/10.1073/pnas.95.4.1460); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC19045/), Eq. 1 and its definitions (total $\Delta G^\circ_{37}$ with the two initiation parameters, ten NN terms and the symmetry term $+0.43$ kcal/mol for self-complementary duplexes), Eq. 2 ($\Delta G=\Delta H-T\Delta S$), Fig. 1 (worked example), Tables 1–2 (unified parameters and symmetry correction $-1.4$ e.u., with the Table 1 footnote on the initiation format); the displayed equations are rendered as images and were reconstructed from the surrounding definitions.
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/) (context only).
