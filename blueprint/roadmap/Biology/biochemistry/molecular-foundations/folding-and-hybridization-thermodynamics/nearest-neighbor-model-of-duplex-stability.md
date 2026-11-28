# Nearest-neighbor model of DNA duplex stability

The nearest-neighbor model of SantaLucia's unified parameters decomposes the standard free energy of forming a Watson–Crick DNA duplex into empirical stacking terms for its adjacent base-pair doublets, initiation contributions tied to the terminal base pairs, and a symmetry correction for self-complementary duplexes; the source evaluates it with tabulated values for a duplex with one G·C and one A·T end.

**Stack counts.** A duplex of $n\ge2$ base pairs is written as a top strand $5'\to3'$ paired antiparallel with its Watson–Crick complement. Each pair of adjacent base pairs is one of the ten distinct nearest-neighbor (NN) doublets $AA/TT$, $AT/TA$, $TA/AT$, $CA/GT$, $GT/CA$, $CT/GA$, $GA/CT$, $CG/GC$, $GC/CG$, $GG/CC$ (a doublet and its reverse complement are the same doublet). Let $n_i$ be the number of occurrences of doublet $i$ ($\sum_in_i=n-1$). The strand is **self-complementary** if it equals its own reverse complement (so the duplex is formed from two identical strands); both ends of such a duplex then carry the same kind of terminal pair.

**Printed decomposition.** The source prints the model symbolically (its Eq. 1) as

$$\Delta G^\circ(\mathrm{total})=\sum_{i}n_i\,\Delta G^\circ(i)+\Delta G^\circ(\text{init w/term G·C})+\Delta G^\circ(\text{init w/term A·T})+\Delta G^\circ(\mathrm{sym}).$$

**Evaluated scope.** With tabulated values, both initiation terms are entered once in the source's worked example, a duplex with one G·C-terminated end and one A·T-terminated end (not self-complementary). For that terminal-pair class this page takes

$$\Delta G^\circ_{37}=\sum_{i}n_i\,\Delta G^\circ_{37}(i)+\Delta G^\circ_{37}(\text{init w/term G·C})+\Delta G^\circ_{37}(\text{init w/term A·T}),$$

and $\Delta H^\circ$, $\Delta S^\circ$ are summed in the same form from the enthalpy and entropy tables. For a duplex whose two ends carry the same kind of terminal pair (every self-complementary duplex among them), the initiation contribution is treated here as a supplied input; no counting rule for it is claimed. At any temperature $T$ in kelvin $\Delta G^\circ_T=\Delta H^\circ-T\Delta S^\circ$ (an identity; using tabulated $\Delta H^\circ,\Delta S^\circ$ far from 37 °C additionally assumes no heat-capacity change).

**Symmetry correction.** Separately, the source reports the correction for self-complementary duplexes, entered once: $\Delta H^\circ(\mathrm{sym})=0$ and $\Delta S^\circ(\mathrm{sym})=-1.4$ cal mol$^{-1}$K$^{-1}$, so $\Delta G^\circ_{37}(\mathrm{sym})=+0.43$ kcal/mol; it is $0$ for other duplexes.

**Status.** The parameters are empirical fits to melting data referred to 1 M NaCl (the oligomer and polymer data sets were fitted separately and should not be interchanged), salt corrections are outside this page, and use of the model for a given duplex assumes two-state melting. Predictions are empirical estimates, not theorems. The source's Table 1 defers the format of the initiation parameters to its ref. 22, which was not read.

## Context

Undergraduate to graduate biochemistry. NN parameters are the basis of melting-temperature and hybridization-energy prediction for primers, probes, antisense and RNA-interference strands, and, with RNA parameters, of secondary-structure energy models such as the [additive energy of the McCaskill partition function](../../../bioinformatics/mccaskill-partition-function-for-rna-folding/energy.md). Designed RNA assemblies, such as the RNA-triple-helix nanoparticles of Conde et al. (2016), are assessed by melting; this DNA model is background for such design but is not the RNA or triplex energy model those strands require.

## Depends on

None.

## Proof depends on

None.

## Expansion

Worked check: for the source's example $5'$-CGTTGA-$3'$ paired with its complement (ends C·G and A·T, so each initiation term occurs once; doublets CG/GC, GT/CA, TT/AA$=$AA/TT, TG/AC$=$CA/GT, GA/CT; not self-complementary), the unified $\Delta G^\circ_{37}$ values sum to $-7.36$ kcal/mol for the stacks and $+0.98+1.03$ for initiation, giving $-5.35$ kcal/mol as in the source's Fig. 1.

A possible convention, not adopted here, would count one initiation term per duplex end; the worked example above has one end of each kind and cannot test it.

Remaining decomposition before the page can be marked ready: (i) a source that states, in readable form, how initiation is applied when both ends carry the same kind of terminal pair (the 1998 paper's ref. 22 or a later unified review), before same-class duplexes can be evaluated on this page; (ii) definition pages for the doublet-count map from sequences to $\mathbb N^{10}$ and for self-complementarity; (iii) separate model pages for salt corrections and for RNA and triplex parameters. The identifiability of the ten doublet parameters from melting data is the subject of [rank deficiency of the nearest-neighbor stacking matrix](rank-deficiency-of-the-nearest-neighbor-stacking-matrix.md).

## Sources

- J. SantaLucia Jr., "A unified view of polymer, dumbbell, and oligonucleotide DNA nearest-neighbor thermodynamics", *Proceedings of the National Academy of Sciences USA* 95(4) (1998), 1460–1465, [doi.org](https://doi.org/10.1073/pnas.95.4.1460); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC19045/), Eq. 1 and its definitions (total $\Delta G^\circ_{37}$ with the two initiation parameters, ten NN terms and the symmetry term $+0.43$ kcal/mol for self-complementary duplexes), Eq. 2 ($\Delta G=\Delta H-T\Delta S$), Fig. 1 (worked example), Tables 1–2 (unified parameters and symmetry correction $-1.4$ e.u., with the Table 1 footnote on the initiation format); the displayed equations are rendered as images and were reconstructed from the surrounding definitions.
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/) (context only).
