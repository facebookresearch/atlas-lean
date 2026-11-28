# Dosing and sampling the same tissue site with one platform

A hydrogel microneedle platform was used for two functions in the same study, in separate experiments: patches loaded with nanoparticles delivered an immunomodulatory agent into tumor-bearing skin, and separate empty patches applied afterwards captured cells from interstitial fluid for analysis off the device.

What the source reports, by experiment:

- *Therapy arm.* Nanoparticle-loaded patches were applied on a repeated schedule in an orthotopic murine melanoma model and in a subcutaneous murine colorectal model, with reduced tumor growth and extended humane survival relative to control patches.
- *Sampling arm, innate phase.* After treatment, *empty* patches were applied for 24 h and then digested; roughly 1,000 CD45+ cells per patch were recovered and analyzed by flow cytometry away from the device. Macrophage frequencies in patch-recovered fluid increased after treatment, with the same direction seen in tumor lysates.
- *Sampling arm, adaptive phase.* In the MC38 model, sampled fluid from serial loaded patches was analyzed over time. The CD8+ to CD4+ ratio pooled from two late timepoints increased but was not statistically significant. The authors discuss low effector-T-cell frequencies; this is an interpretation, not an established explanation of the test result.
- *What the device does not do.* Detection is not performed on the patch; the patch captures material that is analyzed afterwards. Captured cells report the local site, not a systemic compartment.

## Context

Research level. The platform supports both of the group's skin programs - immunostimulation in tumors and immunoregulation in autoimmunity and transplantation - and monitoring is what could make a local dosing strategy adjustable.

## Depends on

- [Recruit and expand: a two-signal local strategy for Treg](./recruit-and-expand-local-treg-strategy.md)

## Proof depends on

None.

## Expansion

To be quantitative this needs: a capture model relating recovered cells to local tissue composition, with efficiency and its variability; calibration with limits of detection and quantification; the time resolution achievable by repeated application; and, if a readout is to drive dosing, a control formulation with the measurement delay made explicit. The non-significant ratio result shows that the sampling arm's sensitivity is itself a quantity to be characterized.

## Sources

- P. Dosta, N. Puigmal, A. M. Cryer, A. L. Rodriguez, E. Scott, R. Weissleder, M. A. Miller, N. Artzi, "Polymeric microneedles enable simultaneous delivery of cancer immunomodulatory drugs and detection of skin biomarkers", *Theranostics* 13(1):1-15 (2023). DOI 10.7150/thno.73966. Read: PubMed Central full text PMC9800729 - therapy sections with Figures 3 and 4 (orthotopic melanoma and subcutaneous colorectal models, repeated application schedule, tumour growth and humane survival), and the section "Non-invasive cell sampling using HA-based MNs allows longitudinal monitoring of immunotherapy response" with Figure 6A-F (empty patches applied after therapy, roughly 1,000 CD45+ cells per patch, macrophage frequencies, serial sampling, pooled CD8+/CD4+ ratio not statistically significant). https://pmc.ncbi.nlm.nih.gov/articles/PMC9800729/
