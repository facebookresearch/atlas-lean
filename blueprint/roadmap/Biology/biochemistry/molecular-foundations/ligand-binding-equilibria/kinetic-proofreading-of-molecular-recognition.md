# Kinetic proofreading of molecular recognition

Kinetic proofreading is a nonequilibrium scheme in which an energy-driven step between two enzyme–substrate complexes gives a wrong substrate a second chance to dissociate, so that the error rate (wrong to right product formation) can fall below the source's equilibrium reference scale, of order $e^{-\Delta}$ for a binding free-energy difference $\Delta$ in units of $k_BT$, toward order $e^{-2\Delta}$.

**Setting (as in Murugan, Huse and Leibler, Fig. 1).** An enzyme $E$ chooses between a right substrate $R$ and a wrong substrate $W$; write $S$ for either. Each substrate can bind to form either of two complexes, $ES^{*}$ and $ES$: the network has direct binding edges $E+S\rightleftharpoons ES^{*}$ and $E+S\rightleftharpoons ES$, an interconversion $ES^{*}\rightleftharpoons ES$ coupled to an external out-of-equilibrium reaction (for example nucleotide hydrolysis), and product formation $ES\to E+P_S$. The two substrates differ only by a binding free-energy difference $\Delta=(G_{EW}-G_{ER})/k_BT>0$ between their complexes.

**Claims recorded for expansion.**

1. *Reference equilibrium discrimination.* The source states: "If the enzyme executes all reactions at equilibrium, the error rate is given simply by the Boltzmann factor, $\eta\sim e^{-\Delta}$." This is the reference against which proofreading is measured; the page records it at that order-of-magnitude level and does not recast it as an occupancy ratio (a network with a live irreversible product step is not literally at detailed balance, so the precise limiting sense is part of the expansion).
2. *Driven error rate.* For driven steady product formation define the error rate $\eta=J_W/J_R$ (wrong to right product flux, $J_R>0$; the wrong-product fraction is $\eta/(1+\eta)$). In the kinetic limits that Murugan et al. state as their conditions [1] (in which $E+S\rightleftharpoons ES^{*}$ equilibrates rapidly and $ES$ is reached mainly through $ES^{*}$ rather than directly from $E$), both substrates cycle many times around the loop $E\to ES^{*}\to ES\to E$, $\eta$ approaches the order $e^{-2\Delta}$, and the mean time to make one correct product becomes long compared with the network's reaction times.

This page is a node to expand: the exact rate-constant inequalities [1] and the expressions for $\eta$ and the completion time [2] are rendered as images in the copy read and are not reproduced here, so the claims are recorded at the order-of-magnitude level stated in the text.

## Context

Graduate to research level. Proofreading explains how biological recognition (codon reading, aminoacyl-tRNA charging, DNA replication) achieves specificity beyond what an equilibrium free-energy difference allows, at a cost in time and dissipated energy. It is a conceptual prerequisite for any discussion of sequence specificity in nucleic-acid or receptor recognition.

## Depends on

- [Equilibrium occupancy of one class of independent binding sites](single-class-binding-isotherm.md)

## Proof depends on

None.

## Expansion

Remaining decomposition before any statement here can become a theorem page: (i) a definition page for the reaction network of Murugan et al. Fig. 1 as a mass-action system or continuous-time Markov chain with explicit rate constants, including the driving step; (ii) a definition of the steady-state product fluxes $J_R,J_W$ and of $\eta$, and of the readout used for the equilibrium comparison; (iii) the source's conditions [1] stated as explicit inequalities; (iv) a proof that under (iii) $\eta$ tends to the square of the single-step discrimination factor, with the completion-time expression [2]. The equilibrium discrimination magnitudes quoted by Murugan et al. ($10^{-4}$ for base pairing, $10^{-2}$ for protein synthesis) are empirical, not consequences of the model. Hopfield's original paper (abstract only read) is cited for the principle; its own reaction labels may differ from Murugan et al.'s and are not used here.

## Sources

- A. Murugan, D. A. Huse and S. Leibler, "Speed, dissipation, and error in kinetic proofreading", *Proceedings of the National Academy of Sciences USA* 109(30) (2012), 12034–12039, [doi.org](https://doi.org/10.1073/pnas.1119911109); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3409783/), section "Hopfield's Kinetic Proofreading Scheme": Fig. 1 (network), the definition of $\eta$ as the rate of producing $P_W$ relative to $P_R$, the equilibrium comparison $\eta\sim e^{-\Delta}$, conditions [1] and Fig. 2A ($\eta\sim e^{-2\Delta}$ with a long completion time), and Eq. [2] (images).
- J. J. Hopfield, "Kinetic proofreading: a new mechanism for reducing errors in biosynthetic processes requiring high specificity", *Proceedings of the National Academy of Sciences USA* 71(10) (1974), 4135–4139, [doi.org](https://doi.org/10.1073/pnas.71.10.4135); only the abstract was accessible as text ([pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC434344/)); cited for the principle of a strongly but nonspecifically driven proofreading pathway.
