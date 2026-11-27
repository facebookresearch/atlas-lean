# Binding of double commitments under Module-SIS

Let $\mathsf{Com}_A(w)=Aw$ and $\mathsf{Com}_D(v)=Dv$ be Ajtai commitments. For a matrix of commitments $C=(\mathsf{Com}_A(w_1),\dots,\mathsf{Com}_A(w_k))$, the *double commitment* is $\mathsf{Com}_D(G^{-1}(C))$, where $G^{-1}$ denotes the balanced gadget decomposition of all entries of $C$ into small-norm ring elements. If both $A$ and $D$ define binding commitments for the relevant norm bounds (Module-SIS hardness), then the double commitment is binding for the tuple $(w_1,\dots,w_k)$ of small-norm witnesses, and its size is that of a single commitment rather than $k$ commitments.

## Proof sketch

Two distinct openings either give distinct decompositions $G^{-1}(C)\ne G^{-1}(C')$ with equal image under $D$, which yields a short kernel vector of $D$, or equal decompositions, hence equal $C$, and then distinct $w_i$ with equal image under $A$, a short kernel vector of $A$. Uniqueness of the balanced decomposition links $C$ and $G^{-1}(C)$.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Proof depends on

- [Relaxed binding of Ajtai commitments with challenge-difference openings](ajtai-relaxed-binding.md)
- [Base-b decomposition commutes with Ajtai commitments](gadget-decomposition-commitments.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems", CRYPTO (2025), IACR ePrint 2025/247.
