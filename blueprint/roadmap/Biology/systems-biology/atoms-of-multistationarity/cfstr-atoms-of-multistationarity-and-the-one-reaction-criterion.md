# CFSTR atoms of multistationarity and the one-reaction criterion

**Definitions.** A *continuous-flow stirred-tank reactor* (CFSTR) is a reaction network containing every outflow reaction $X_i \to 0$; it is *fully open* if it also contains every inflow $0 \to X_i$. A fully open CFSTR is a *CFSTR atom of multistationarity* if it admits multiple nondegenerate positive mass-action steady states and is minimal with respect to the embedded-network relation among fully open CFSTRs with this property.

**Theorem (one non-flow reaction).**
1. A CFSTR whose only non-flow reaction is $a_1X_1 + \dots + a_sX_s \to b_1X_1 + \dots + b_sX_s$ admits multiple positive mass-action steady states if and only if
$$\sum_{i:\ b_i > a_i} a_i > 1,$$
and then it admits multiple nondegenerate ones.
2. If the only non-flow reactions are the reversible pair $a \cdot X \rightleftarrows b \cdot X$, it is multistationary if and only if $\sum_{b_i > a_i} a_i > 1$ or $\sum_{a_i > b_i} b_i > 1$.

**Theorem (atoms).**
1. A fully open CFSTR possesses a CFSTR atom of multistationarity (as an embedded network) if and only if it admits multiple nondegenerate positive mass-action steady states.
2. A one-reaction fully open CFSTR is an atom if and only if its non-flow reaction is $a_1 X \to a_2 X$ with $a_2 > a_1 > 1$, or $X + Y \to b_1 X + b_2 Y$ with $b_1 > 1$ and $b_2 > 1$.
3. Of the $386$ reversible, bimolecular, two-reaction fully open CFSTRs, exactly $35$ are multistationary, each with nondegenerate steady states and a unique minimal multistationary subnetwork; under the embedded-network order these have $11$ minimal elements, the bimolecular two-reaction atoms. A bimolecular two-reaction fully open CFSTR is multistationary if and only if it contains one of these $11$ atoms as an embedded network.

## Depends on

- [Lifting multistationarity from subnetworks and embedded networks](lifting-multistationarity-from-subnetworks-and-embedded-networks.md)

## Expansion

Every multistationary fully open CFSTR has a minimal multistationary embedded CFSTR because the embedded-network order is well-founded, and conversely any atom it contains lifts back by the embedded-network lifting theorem; this gives the "atoms characterize multistationarity" statement. For a single reaction $a\cdot X \to b\cdot X$ with flows, eliminating all but one variable reduces the steady-state equations to a one-variable polynomial whose number of positive roots is controlled by the reactant coefficients of species that are net-produced; the atoms are the minimal reactions achieving $\sum_{b_i > a_i} a_i \ge 2$. The two-reaction classification is a finite enumeration combined with these criteria and the lifting results.

## Sources

- B. Joshi, A. Shiu, "Atoms of multistationarity in chemical reaction networks", arXiv:1108.5238 (2011), Theorem 2.11 (citing Joshi's one-reaction classification), Definition 5.1, Corollaries 5.2–5.3, Theorem 7.1 and Corollary 7.2, <https://doi.org/10.48550/arXiv.1108.5238>.
