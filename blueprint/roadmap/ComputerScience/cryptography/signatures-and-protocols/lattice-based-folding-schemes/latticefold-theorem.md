# LatticeFold: post-quantum folding for CCS from Module-SIS

Let $R_q$ be a power-of-two cyclotomic ring with a strong sampling set of short challenges, possibly over a small (e.g., 64-bit) prime field via ring packing. There is a folding scheme for linearized and committed CCS relations over $R_q$ with Ajtai commitments, in which each fold consists of (i) a decomposition step splitting witnesses into base-$b$ digits, (ii) a sum-check-based range proof that all digits are small, and (iii) a linear-combination fold with short challenges, so that the norm of the running witness is bounded independently of the number of folds. The scheme is complete and knowledge sound assuming the Module-SIS problem is hard for the corresponding norm bound, and is plausibly post-quantum; it supports high-degree CCS and yields IVC/PCD as in HyperNova.

## Proof sketch

Decomposition keeps norms small; the range proof certifies that the decomposed digits are indeed small, which is necessary because the verifier cannot see the witness. Knowledge soundness combines sum-check soundness, relaxed binding of Ajtai commitments (reducing double openings to Module-SIS), and extraction across challenge differences, whose invertibility follows from the strong sampling set property.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)
- [Folding scheme for an NP relation](../relaxed-r1cs-folding-schemes/folding-scheme.md)

## Proof depends on

- [Base-b decomposition commutes with Ajtai commitments](gadget-decomposition-commitments.md)
- [Sum-check range proof via a vanishing product](sumcheck-range-check.md)
- [Worst-case norm bounds for folding lattice witnesses without norm reduction](lattice-folding-norm-growth.md)
- [HyperNova multi-folding scheme for CCS](../customizable-constraint-systems-and-multi-folding/hypernova-multifolding.md)
- [Relaxed binding of Ajtai commitments with challenge-difference openings](ajtai-relaxed-binding.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", ASIACRYPT (2025), IACR ePrint 2024/257.
