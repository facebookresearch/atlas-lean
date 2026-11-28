# Generalized phase locking value as the leading singular value of a spike–LFP coupling matrix

Record $n_s$ spiking units and $n_c$ local field potential (LFP) channels over $K$ trials. Band-pass filter the LFPs around frequency $f$ and form their analytic signals $L^{(k)}_n(t)$ with phases $\phi^{(k)}_n(t)$. Unit $m$ fires at times $t^{m,(k)}_j$, with $N_m$ spikes in total. The **spike–LFP coupling matrix** $C \in \mathbb C^{n_c \times n_s}$ is

$$C_{n,m} = \frac{1}{N_m}\sum_{k=1}^K \sum_{j} \exp\bigl(i\,\phi^{(k)}_n(t^{m,(k)}_j)\bigr) \quad\text{or}\quad C_{n,m} = \frac{1}{N_m}\sum_{k=1}^K \sum_{j} L^{(k)}_n(t^{m,(k)}_j),$$

whose entries are the classical pairwise phase-locking values (PLVs) or their amplitude-weighted versions. Write the singular value decomposition $C = \sum_{k=1}^p d_k u_k v_k^{H}$ with $d_1 \ge d_2 \ge \cdots > 0$.

**Definition (GPLA).** Generalized phase locking analysis summarizes $C$ by its best rank-one approximation $C \approx d_1 u_1 v_1^{H}$ (Eckart–Young). The **generalized PLV** is $\mathrm{gPLV} = d_1$; the **LFP vector** $u_1$ and **spike vector** $v_1$ give, through their moduli and phases, the spatial pattern of the field oscillation and how strongly and at what phase each unit is locked. Normalizing $u_1$ and $v_1$ so their mean phase difference is $\Phi_d$, the complex gPLV $\mathrm{gPLV}\,e^{-i\Phi_d}$ plays the role of the univariate PLV with its locking phase. With one LFP channel, $\mathrm{gPLV}$ combines the units' individual couplings without assuming they share a locking phase, unlike pooling all spikes.

**Significance (random-matrix test).** After whitening the LFPs across channels, in the absence of coupling and for Poisson-like spiking, the squared singular values of the suitably normalized $C$ asymptotically follow the Marchenko–Pastur law. Its upper edge, which depends only on the matrix dimensions, is the threshold: $d_1^2$ above it indicates significant multivariate coupling, and the number of squared singular values above it estimates the number of distinct coupled populations and rhythms. The test needs no surrogate data and no multiple-comparison correction across the $n_c n_s$ pairs, and its power does not degrade as the channel count grows.

## Expansion

Each column of $C$ is one unit's coupling profile across channels and each row one channel's profile across units. If spiking is modulated by a single global oscillation with a fixed spatial pattern, $C$ is approximately rank one plus estimation noise from the finite number of spikes, so the leading singular triplet recovers the pattern and its strength optimally in the least-squares sense. Whitening makes the null-hypothesis entries approximately i.i.d., which is what brings in the Marchenko–Pastur law. In linearized two-population (excitatory–inhibitory) neural field models, linear response theory relates the phases of the spike and LFP vectors to the network's recurrent inhibition, so gPLV and the phase shift between the vectors become interpretable as properties of the underlying circuit.

## Sources

- S. Safavi, T. I. Panagiotaropoulos, V. Kapoor, J. F. Ramirez-Villegas, N. K. Logothetis, M. Besserve, "Uncovering the organization of neural circuits with Generalized Phase Locking Analysis", PLoS Computational Biology (2023), Eqs. (13)–(18) and (26), Results section on random-matrix significance assessment and Materials and methods (Analytical test), <https://doi.org/10.1371/journal.pcbi.1010983>, PMCID PMC10109521.
