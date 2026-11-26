# Flory–Stockmayer percolation threshold for two-component multivalent systems

**Setting.** Two multivalent molecular species interact only heterotypically: each molecule of species $1$ carries $s_1 \ge 2$ stickers and each molecule of species $2$ carries $s_2 \ge 2$ stickers, and a bond forms only between a sticker of species $1$ and a sticker of species $2$. Let $f_1, f_2 \in [0,1]$ be the fractions of stickers of each species that are bound, and $c_1, c_2$ the concentrations.

**Percolation criterion (Flory–Stockmayer).** In the tree-like (no intramolecular loops) mean-field approximation, a system-spanning network forms when

$$f_1 f_2\,(s_1 - 1)(s_2 - 1) > 1 .$$

**Consequences.**

1. Stoichiometric balance: every bond uses one sticker of each species, so $f_1 s_1 c_1 = f_2 s_2 c_2$. A large excess of species $1$ forces $f_1 \to 0$ (and $f_2 \to 1$), and vice versa, so $f_1 f_2 \to 0$ and the network cannot percolate at either extreme of composition.
2. Hence the percolation line in the $(c_1, c_2)$ plane is a bounded, parabola-like curve, and percolation is reentrant: at fixed $c_1$ inside the percolating range, increasing $c_2$ first crosses into and then out of the percolated regime.
3. Lattice simulations of the nucleolar protein N130 ($s_1 = 10$ acidic tracts) with the rpL5 peptide ($s_2 = 2$ arginine motifs) show parabolic percolation lines and closed, ellipse-shaped binodals, so phase separation driven by obligate heterotypic interactions is likewise reentrant and has no composition-independent saturation concentration.

## Expansion

On a Bethe-lattice picture, a bound sticker of species $1$ leads to a species-$2$ molecule, which offers $s_2 - 1$ further stickers, each bound with probability $f_2$, each leading to a species-$1$ molecule offering $s_1 - 1$ stickers bound with probability $f_1$. The expected number of new branches per two steps is $f_1 f_2 (s_1 - 1)(s_2 - 1)$; the branching process is supercritical, giving an infinite cluster, exactly when this exceeds $1$. Because the bound fractions are tied by stoichiometry, the criterion depends on the product $f_1 f_2$, which is maximal near balanced sticker concentrations and vanishes for large excess of either species. In the two-phase regime, tie lines with nonzero slope make the dilute-phase concentration of one species vary with its total concentration, so the single-component notion of a fixed saturation concentration does not carry over.

## Sources

- J.-M. Choi, F. Dar, R. V. Pappu, "LASSI: A lattice model for simulating phase transitions of multivalent proteins", PLoS Computational Biology 15(10) (2019) e1007028, Results ("Percolation lines have parabolic shapes", "Binodals for systems defined by obligate heterotypic interactions will form closed loop ellipses", "Slopes of tie lines ..."), <https://doi.org/10.1371/journal.pcbi.1007028> (PMC6822780).
- P. J. Flory, "Molecular size distribution in three dimensional polymers. I. Gelation", Journal of the American Chemical Society 63 (1941) 3083–3090.
