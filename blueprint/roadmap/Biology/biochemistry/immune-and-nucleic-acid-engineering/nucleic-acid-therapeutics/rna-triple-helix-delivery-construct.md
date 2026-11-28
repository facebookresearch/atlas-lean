# RNA triple-helix construct for co-delivery of two microRNA cargos

Three RNA strands - a microRNA mimic sense strand, its antisense strand, and an antagomiR as the third strand - were reported to assemble into a triple helix, which was complexed with a cationic dendrimer and embedded in an adhesive hydrogel. The intended cargo identities are endogenous microRNA sequences; the strands as used also carry chemical modifications.

What is intended, what is modeled and what is measured:

- *Intended cargo identities.* A mimic of a tumor-suppressor microRNA and an inhibitor of an oncogenic microRNA, carried as one object.
- *Modifications.* The strands used were labeled with dyes and a quencher, and one carried a lipid modification, so the delivered species are modified oligonucleotides rather than bare microRNAs.
- *Modelled structure.* The published depiction of the triple helix is a software model, not a solved structure.
- *Assembly evidence.* Fluorescence quenching between the dye and quencher reports spatial proximity of the strands and became near-complete at equimolar mixing; gel electrophoresis showed slower migration for the three-strand assembly than for two-strand or single strands; melting analysis gave a higher transition temperature for the triplex than for the duplex or single-strand forms. Each assay supports a different aspect, and proximity alone is not structure.
- *Size observations, by method.* Scanning electron microscopy and dynamic light scattering report different quantities; reported values include particles of tens of nanometers and micron-scale aggregates, which were then dispersed in the hydrogel.

This is an engineering result for one formulation. Assembly procedures are deliberately not reproduced here.

## Context

Research level. The construct is the central object of this folder's RNA work: the therapeutic sequences are endogenous, and what the design manipulates is the physical object that carries them. Hydrogel mechanics, adhesion chemistry and release transport are treated in the biomaterials-and-transport subfield.

## Depends on

- [Watson-Crick and Hoogsteen pairing in nucleic-acid therapeutics](./watson-crick-and-hoogsteen-pairing.md)
- [MicroRNA silencing and the mimic/antagomiR pair](./microrna-silencing-pathway.md)

## Proof depends on

None.

## Expansion

Before any mathematical statement: a stoichiometry model relating mixing ratio to assembled fraction, with the plateau identified; a size distribution rather than mean and standard deviation summaries, with the measurement method's bias stated; a stability account separating protection from nuclease attack from reduced accessibility; and an explicit statement of which observable stands for assembly. No manipulation of the reported numbers establishes behavior with another cargo set, tissue or species.

## Sources

- J. Conde, N. Oliva, M. Atilano, H. S. Song, N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3):353-363 (2016). DOI 10.1038/nmat4497. Read: PubMed Central author manuscript PMC6594154 - Figure 1 and caption (including the M-fold-modelled structure in 1b and the reported particle and aggregate sizes by scanning electron microscopy); the optimisation section (dynamic light scattering value; hierarchical length scales; strand modifications); Figure 2a (quenching at equimolar ratio), Figure 2c (gel electrophoresis) and Figure 2d (melting temperatures of triplex, duplex and single-strand forms). https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/
