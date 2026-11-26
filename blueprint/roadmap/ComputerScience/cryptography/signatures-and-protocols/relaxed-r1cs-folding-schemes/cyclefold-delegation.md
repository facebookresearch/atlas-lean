# CycleFold: delegating non-native scalar multiplications to a secondary folded instance

In folding-based IVC over a 2-cycle $(E_1,E_2)$, the folding verifier circuit $C_V$ over the scalar field of $E_1$ performs its field and hash operations natively, but its few elliptic-curve scalar multiplications on $E_1$ (one scalar multiplication followed by a point addition in HyperNova's verifier, two in Nova's) would need arithmetic over the base field of $E_1$. CycleFold delegates each such operation to one invocation of a small circuit $C_{\mathrm{EC}}$ over the scalar field of $E_2$, which equals the base field of $E_1$, so $C_{\mathrm{EC}}$ computes the operation without field emulation and exposes its inputs and output as public IO. At each step $C_V$ takes as advice a committed instance $u_{\mathrm{EC}}$ of $C_{\mathrm{EC}}$ for each delegated operation, checks that its inputs are the ones the verifier needs, uses its output in place of the scalar multiplication, and folds $u_{\mathrm{EC}}$ into a running committed relaxed R1CS instance $U_{\mathrm{EC}}$ with Nova's folding scheme, alongside the folding of the main computation. For HyperNova this gives a public-coin multi-folding scheme for $\mathcal{R}_1=\mathrm{LCCCS}\times\mathrm{CRR1CS}$ and $\mathcal{R}_2=\mathrm{CCCS}$ with perfect completeness and knowledge soundness, whose verifier performs $O(d\log m)$ field operations and $O(1)$ group operations; the circuit on the second curve consists only of $C_{\mathrm{EC}}$.

## Proof sketch

Completeness holds because each honest $u_{\mathrm{EC}}$ certifies the group operation the verifier uses, and both foldings are complete. Knowledge soundness combines the extractors of the CCS multi-folding scheme and of Nova's folding scheme for the running secondary instance: an accepting final pair yields witnesses for every folded $u_{\mathrm{EC}}$, so each claimed output of $C_{\mathrm{EC}}$ is the correct group operation, and the extraction for the main computation then proceeds as without delegation.

## Depends on

- [Two-cycles of elliptic curves for recursive arguments](cycle-of-curves.md)
- [Nova: IVC with constant recursion overhead from folding](nova-ivc.md)
- [Folding scheme for an NP relation](folding-scheme.md)
- [Relaxed R1CS instances with slack vector and scalar](relaxed-r1cs.md)
- [Incrementally verifiable computation scheme for an iterated function](../incrementally-verifiable-computation-and-pcd/ivc-scheme.md)

## Proof depends on

- [Nova's folding scheme for committed relaxed R1CS](nova-folding-theorem.md)
- [HyperNova multi-folding scheme for CCS](../customizable-constraint-systems-and-multi-folding/hypernova-multifolding.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573, Section 8 (Section 8.2, Theorem 4, Theorem 2) and Appendix E.
