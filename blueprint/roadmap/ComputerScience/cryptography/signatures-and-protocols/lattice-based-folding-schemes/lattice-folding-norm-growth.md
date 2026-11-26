# Unbounded norm growth obstructs naive lattice folding

Let witnesses satisfy $\|w_1\|_\infty,\|w_2\|_\infty\le B$ and fold as $w=w_1+rw_2$ with $r\in\mathcal{C}$, $\|r\|_{\mathrm{op}}\le\gamma$. Then $\|w\|_\infty\le(1+\gamma)B$, and after $k$ successive folds without norm reduction the bound becomes $(1+\gamma)^{k}B$. Since knowledge soundness of Ajtai commitments requires the extracted witness norm to stay below the Module-SIS bound $\beta< q$, folding with a fixed modulus supports only $O(\log_{1+\gamma}(q/B))$ rounds unless each fold is preceded by a norm-reducing step, such as base-$b$ decomposition together with a range proof.

## Proof sketch

Apply $\|w_1+rw_2\|_\infty\le\|w_1\|_\infty+\|r\|_{\mathrm{op}}\|w_2\|_\infty$ inductively. Extraction of earlier witnesses from later ones multiplies by inverses of challenge differences, which can only increase norms, so the bound on the final witness controls soundness.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)
- [Relaxed binding of Ajtai commitments with challenge-difference openings](ajtai-relaxed-binding.md)

## Proof depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", IACR ePrint 2024/257 (2024).
