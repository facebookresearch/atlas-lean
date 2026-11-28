# The cGAS-STING axis as an engineering target

Cyclic GMP-AMP synthase (cGAS) is activated by binding cytosolic double-stranded DNA and catalyzes synthesis of the cyclic dinucleotide cGAMP from the nucleotides ATP and GTP. cGAMP binds the stimulator of interferon genes (STING) protein, which initiates signaling leading to type I interferon production.

Terms and distinctions used throughout this folder:

- *Activating ligand versus catalytic substrate.* Cytosolic double-stranded DNA is the ligand whose binding activates cGAS; it is not the material from which cGAMP is built. In cell-free extracts, cGAMP synthesis required ATP and GTP and occurred in the presence of DNA but not RNA.
- *Direct agonist versus upstream activator.* A STING agonist binds STING: endogenous 2'3'-cGAMP, or a synthetic cyclic dinucleotide. DNA is an upstream activator of the pathway through cGAS, not a STING agonist.
- *Endogenous production versus exogenous administration.* Agonist can be made inside a cell by cGAS, or supplied from outside as a drug. These differ in location, timing and clearance, and the folder keeps them apart.
- *Cell compartment.* "STING signaling" without naming the cell type (cancer cell, dendritic cell, macrophage, endothelial cell) is ambiguous; in [Cancer cells as a depot: host-cell dependence of a nanoparticle immunotherapy](./nanoparticle-depot-and-host-cell-dependence.md) the compartment decides the result.

cGAMP is hydrophilic and negatively charged, so it does not readily cross membranes, and it is degraded extracellularly by ectonucleotide pyrophosphatase/phosphodiesterase 1 (ENPP1).

## Context

Undergraduate level. This page fixes the vocabulary for the innate-immunity work in this subfield, which spans synthetic agonist delivery, endogenous agonist production inside cancer cells, and conjugate chemistry. It is exposition of established pathway biology as stated in the sources read, not a new result.

## Depends on

None.

## Proof depends on

None.

## Expansion

A quantitative version requires: enzyme kinetics for cGAS as a DNA-activated nucleotidyltransferase acting on ATP and GTP; a receptor-occupancy treatment for STING; the signaling cascade with its feedback and desensitisation; extracellular degradation by ENPP1; and the interferon response as a dynamical output rather than a label. None of that is developed here.

## Sources

- J. Wu, L. Sun, X. Chen, F. Du, H. Shi, C. Chen, Z. J. Chen, "Cyclic-GMP-AMP Is An Endogenous Second Messenger in Innate Immune Signaling by Cytosolic DNA", *Science* 339(6121):826-830 (2013). DOI 10.1126/science.1229963. Read: PubMed Central author manuscript PMC3855410, Abstract ("synthesized cyclic-GMP-AMP (cGAMP) in vitro from ATP and GTP in the presence of DNA but not RNA") and the Results paragraph accompanying Figure 3 stating that ATP and GTP were both necessary and sufficient to support synthesis of the IRF3 activator. https://pmc.ncbi.nlm.nih.gov/articles/PMC3855410/
- L. Sun, J. Wu, F. Du, X. Chen, Z. J. Chen, "Cyclic GMP-AMP synthase is a cytosolic DNA sensor that activates the type I interferon pathway", *Science* 339(6121):786-791 (2013). DOI 10.1126/science.1232458. Read: PubMed record 23258413, Abstract ("cGAS bound to DNA in the cytoplasm and catalyzed cGAMP synthesis"; cGAS identified as a nucleotidyltransferase-family enzyme). https://pubmed.ncbi.nlm.nih.gov/23258413/
- A. M. Cryer, P. Dosta, M. Z. Dion, L. de la Parra Soto, E. Amar-Lewis, G. Garcia de Leon Carmona, A. A. Espinosa Perez, D. F. Ruiz Aguilar, T. Huerta, B. Nicolas Ruiz, N. N. Casteele Hernandez, Y. Soria, N. Artzi, "Restoration of cGAS in cancer cells promotes antitumor immunity via transfer of cancer cell-generated cGAMP", *PNAS* 122(45):e2409556122 (2025). DOI 10.1073/pnas.2409556122. Read: PubMed Central full text PMC12625989, Significance statement and Introduction paragraph identifying 2'3'-cGAMP as the endogenous STING ligand produced by cGAS on recognition of cytoplasmic double-stranded DNA, and noting its charge, poor cell entry and degradation by ENPP1. https://pmc.ncbi.nlm.nih.gov/articles/PMC12625989/
