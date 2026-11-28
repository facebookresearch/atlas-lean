# Extracellular cGAMP and bystander activation

A second messenger made inside one cell can act on another. The source states that cGAMP derived from cancer cells can act on proximal immune cells and activate STING in them, and reports immune activation through a combination of extracellular transfer and cell-cell contact, without assigning the observed responses to any particular transport route.

Scope, with direction and species kept explicit:

- *What the cited experiment shows.* Activation of immune cells by cancer-cell-derived material, assessed with conditioned medium and coculture; the source does not attribute those responses to a named transporter.
- *Routes named in the literature the source cites.* Transfer between cells via gap junctions, viral particles and extracellular vesicles; membrane proteins that mediate export from a cell, and others that mediate import into a cell. These are pointers to cited work, not findings of the melanoma experiment.
- *One named example, with its scope.* SLC46A2 was identified as the dominant cGAMP *importer* in primary human monocytes and in human monocyte-derived macrophages; in the same study, monocytes and M1-polarized macrophages were shown to sense tumor-derived extracellular cGAMP in murine tumors. Import and export are different directions and are not interchangeable.
- *Degradation.* Extracellular cGAMP is degraded by ENPP1, so transfer competes with hydrolysis.

Nothing here states what fraction of produced cGAMP leaves a cell, how far it travels, or how long it persists outside.

## Context

Graduate level. The page separates a mechanism from the therapy built on it, so [Making the tumor cell produce its own innate-immune agonist](./cancer-cell-cgas-restoration.md) can be read as an application. It is also the biological precedent for the more general framing in [The paracrine transfer effect as a nanomedicine design concept](./paracrine-transfer-effect.md).

## Depends on

- [The cGAS-STING axis as an engineering target](./cgas-sting-sensing-axis.md)
- [Species, model system and the scope of a preclinical claim](../preclinical-model-systems/species-and-model-system-scope.md)

## Proof depends on

None.

## Expansion

A model would require: export and import fluxes per cell with transporter-specific kinetics and stated cell types; extracellular degradation; a spatial component, since "proximal" is geometric; and a threshold for downstream activation. Supplying those would make bystander activation quantitative; without them it supports qualitative reasoning only.

## Sources

- A. M. Cryer, P. Dosta, M. Z. Dion, et al., N. Artzi, "Restoration of cGAS in cancer cells promotes antitumor immunity via transfer of cancer cell-generated cGAMP", *PNAS* 122(45):e2409556122 (2025). DOI 10.1073/pnas.2409556122. Read: PubMed Central full text PMC12625989 - Abstract (extracellular transfer and cell-cell contact), Introduction paragraph listing gap junctions, viral particles and extracellular vesicles as reported transfer mechanisms and noting export and entry transporters and ENPP1-mediated degradation, and Figure 3, which does not assign the observed responses to a named route. https://pmc.ncbi.nlm.nih.gov/articles/PMC12625989/
- A. F. Cordova, C. Ritchie, V. Bohnert, L. Li, "Human SLC46A2 Is the Dominant cGAMP Importer in Extracellular cGAMP-Sensing Macrophages and Monocytes", *ACS Central Science* 7(6):1073-1088 (2021). DOI 10.1021/acscentsci.1c00440. Read: PubMed record 34235268, Abstract (SLC46A2 as dominant importer in primary human monocytes and in monocyte-derived macrophages; monocytes and M1-polarised macrophages sensing tumour-derived extracellular cGAMP in murine tumours). https://pubmed.ncbi.nlm.nih.gov/34235268/
