# CFSTR atoms of multistationarity and the bimolecular two-reaction classification

**Definitions.** A *continuous-flow stirred-tank reactor* (CFSTR) is a reaction network containing every outflow reaction $X_i \to 0$; it is *fully open* if it also contains every inflow $0 \to X_i$. A fully open CFSTR is a *CFSTR atom of multistationarity* if it admits multiple nondegenerate positive mass-action steady states and is minimal with respect to the embedded-network relation among fully open CFSTRs with this property.

**Theorem.**
1. *(Atoms characterize multistationarity.)* A fully open CFSTR possesses a CFSTR atom of multistationarity (as an embedded network) if and only if it admits multiple nondegenerate positive mass-action steady states.
2. *(Bimolecular two-reaction atoms.)* Of the $386$ reversible, bimolecular, two-reaction fully open CFSTRs, exactly $35$ admit multiple positive mass-action steady states; each of these admits multiple nondegenerate ones and contains a unique minimal multistationary subnetwork, and under the embedded-network relation these $35$ subnetworks have $11$ minimal elements, which are the bimolecular two-reaction CFSTR atoms of multistationarity.
3. *(Classification.)* A bimolecular, two-reaction fully open CFSTR admits multiple nondegenerate positive mass-action steady states if and only if it contains one of the $35$ minimal subnetworks as a sub-CFSTR, if and only if it contains one of the $11$ atoms as an embedded network. A fully open CFSTR with any number of reactions, not necessarily bimolecular, that contains one of the $35$ as a sub-CFSTR or one of the $11$ atoms as an embedded network admits multiple nondegenerate positive mass-action steady states.

The one-reaction atoms, and the arithmetic criterion for multistationarity of a fully open network with one non-flow reaction, are on [Multistationarity of fully open networks with one non-flow reaction](../multistationarity-of-fully-open-networks/multistationarity-of-fully-open-networks-with-one-non-flow-reaction.md).

## Depends on

- [Lifting multistationarity from subnetworks and embedded networks](lifting-multistationarity-from-subnetworks-and-embedded-networks.md)
- [Multistationarity of fully open networks with one non-flow reaction](../multistationarity-of-fully-open-networks/multistationarity-of-fully-open-networks-with-one-non-flow-reaction.md)

## Expansion

Every multistationary fully open CFSTR has a minimal multistationary embedded CFSTR because the embedded-network order is well-founded, and conversely any atom it contains lifts back by the embedded-network lifting theorem; this gives part 1. The two-reaction classification is a finite enumeration of the $386$ networks, each settled by the one-reaction criterion applied to embedded networks, by the lifting results, or by explicit steady-state computations; part 3 then follows from parts 1 and 2 and the lifting theorems.

## Sources

- Badal Joshi and Anne Shiu, "Atoms of multistationarity in chemical reaction networks", Journal of Mathematical Chemistry (2012), <https://doi.org/10.1007/s10910-012-0072-0>; numbering as in arXiv:1108.5238: Definition 5.1, Corollary 5.2, Theorem 7.1 and Corollary 7.2.
