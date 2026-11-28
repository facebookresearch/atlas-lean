# Co-packaging gene silencing, a drug and photothermal ablation in one local device

A hydrogel patch carried two nanoparticle populations: one bearing short interfering RNA against a driver oncogene, one bearing an antibody drug and able to convert near-infrared light into heat. Co-packaging is not simultaneity: the reported treatment is described as two waves, with gene knockdown first and drug release with ablation on irradiation.

Reported components and results, kept in their own settings:

- *Carriers.* Gold nanospheres carrying short interfering RNA against *Kras*, and gold nanorods carrying bevacizumab; both functionalized with a tumor-targeting peptide, with a fusogenic peptide added to the RNA carrier.
- *Photothermal selectivity, measured in solution.* The reported comparison showed heating for the nanorod population but not the nanosphere population under the tested conditions. This is a solution measurement, not a tissue result; irradiation settings are not reproduced here.
- *Release.* Antibody release from the nanorods was reported in vitro following irradiation. This does not establish an in vivo release fraction.
- *Cell-level results.* The study reports knockdown in a human colorectal cancer cell line and cell death for irradiated drug-bearing nanorods and the combined-carrier condition, not for carriers generally. These cell assays are distinct from the solution and animal experiments.
- *Animal work.* SCID hairless congenic mice carried LoVo-Luc human colorectal xenografts in separate resection and non-resection cohorts. The non-resected cohort included a bioluminescence observation fifteen days after implantation. Recurrence in the resection cohort is a different endpoint. Percentages and survival p-values are not reproduced without their specific reference and contrast.

Photothermal physics belongs to the physics-transport prerequisites and is not developed here; no procedures are reproduced.

## Context

Research level. The page is the subfield's worked example of multimodality and of scheduling: order is a design variable independent of dose, and the selectivity argument shows a physical property being used to address one subpopulation of a mixed formulation.

## Depends on

- [MicroRNA silencing and the mimic/antagomiR pair](./microrna-silencing-pathway.md)
- [Species, model system and the scope of a preclinical claim](../preclinical-model-systems/species-and-model-system-scope.md)

## Proof depends on

None.

## Expansion

What is missing before a mathematical statement: a declared non-interaction reference against which a three-modality combination could be judged, since the source reports arm comparisons; a heating model with geometry and perfusion, which an in-solution measurement does not supply; a release function with stated form and uncertainty rather than one percentage at one exposure time; biodistribution, since relative uptake in culture does not establish selectivity in tissue; and cohort-resolved reporting, since resected and non-resected animals answer different questions.

For the choice of non-interaction reference, see [Interaction references are not interchangeable](../../../pharmacokinetics/pharmacodynamic-response-models/interact-references-disagree.md).

## Sources

- J. Conde, N. Oliva, Y. Zhang, N. Artzi, "Local triple-combination therapy results in tumour regression and prevents recurrence in a colon cancer model", *Nature Materials* 15(10):1128-1138 (2016). DOI 10.1038/nmat4707. Read: PubMed Central author manuscript PMC6594055 - "The design of local triple-combination therapy" (carrier geometry, targeting and fusogenic peptides, the two-wave rationale); "Functional characterization and in vitro performance" with Figure 2a-f (absorbance peaks; 808 nm and 1 W heating in solution; release at 120 s; *Kras* knockdown; uptake comparison; live-dead result restricted to irradiated drug-bearing nanorod and combined conditions); and the in vivo section with Figure 4 (SCID hairless congenic mice, LoVo-Luc xenografts, resection and non-resection cohorts, more than 90% abrogation at day 15 with n = 5 and P < 0.001, recurrence in the hydrogel-alone group, survival comparison reported with P = 0.008). https://pmc.ncbi.nlm.nih.gov/articles/PMC6594055/
