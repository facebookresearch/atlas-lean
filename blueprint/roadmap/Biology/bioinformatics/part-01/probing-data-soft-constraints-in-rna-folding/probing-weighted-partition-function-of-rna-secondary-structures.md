# Probing-weighted partition function of RNA secondary structures

**Data.** Let $a = a_1\cdots a_n$ be an RNA sequence and $q = (q_1,\dots,q_n) \in [0,1]^n$ normalized footprinting data, $q_i$ being interpreted as the probability that nucleotide $i$ is unpaired (SHAPE or in-line probing reactivities are mapped to $[0,1]$ by a piecewise linear normalization; missing positions receive an uninformative value).

**Soft-constraint weights.** For a secondary structure $S$ write $s_i \in \{\text{paired},\text{unpaired}\}$ for the status of nucleotide $i$, let $\delta_i(s_i) \ge 0$ measure the discrepancy between $q_i$ and that status, and fix a scaling parameter $\beta \ge 0$. The per-position Boltzmann weight is $w_i(s_i) = e^{-\beta\,\delta_i(s_i)}$, and the probing weight of $S$ is

$$W_\beta(S) = \prod_{i=1}^{n} w_i(s_i) = e^{-\beta\, d(S,q)}, \qquad d(S,q) = \sum_{i=1}^{n}\delta_i(s_i).$$

**Weighted partition function.** With $E(S)$ the free energy of $S$ in the nearest-neighbour (Turner) loop model, gas constant $R$ and temperature $T$,

$$Z_\beta = \sum_{S} e^{-E(S)/RT}\,W_\beta(S),$$

the sum over all [secondary structures](../../mccaskill-partition-function-for-rna-folding/structures.md) of $a$. For $\beta = 0$ this is McCaskill's partition function for the nearest-neighbour energy (not the additive base-pair energy of the McCaskill partition-function page; loop energies are not additive over base pairs).

**Recursions.** $Z_\beta$ is computed by the McCaskill dynamic programme in which every unpaired run $[i,j]$ contributes the product of the unpaired weights $w_k(\text{unpaired})$, $i \le k \le j$, and every base pair $(i,j)$ contributes $w_i(\text{paired})\,w_j(\text{paired})$, alongside the usual hairpin, interior-loop and affine multiloop Boltzmann factors. Inside and outside passes then give the weighted base-pair probabilities

$$P_\beta(i,j) = \frac{1}{Z_\beta}\sum_{S \ni (i,j)} e^{-E(S)/RT}\,W_\beta(S)$$

at the same asymptotic cost as the unweighted algorithm. Replacing sums by minima, products by sums and weights by the corresponding pseudo-energies yields a minimum free energy algorithm with probing soft constraints.

## Depends on

- [Set of all secondary structures of a sequence](../../mccaskill-partition-function-for-rna-folding/structures.md)

## Expansion

The weights act as an exponential tilt of the Boltzmann ensemble toward structures whose pairing pattern agrees with the reactivities. Because the tilt factorizes over nucleotides, it can be attached to the elementary decisions of the folding recursion (a nucleotide left unpaired or opened as a pair) without changing the recursion's structure. Unlike pseudo-energy schemes that reward only nucleotides in stacked pairs, the weights use the data at unpaired positions as well. The parameter $\beta$ sets the trust in the data and is tuned to maximize prediction accuracy.

## Sources

- K. Zarringhalam, M. M. Meyer, I. Dotu, J. H. Chuang, P. Clote, "Integrating chemical footprinting data into RNA secondary structure prediction", PLoS One (2012), Methods: Boltzmann weights (Eq. (2)), weighted partition function (Definition 1, Eqs. (3)–(8)), <https://doi.org/10.1371/journal.pone.0045160>, PMCID PMC3473038.
