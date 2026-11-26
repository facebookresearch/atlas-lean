# Unbounded norm growth obstructs naive lattice folding

Let witnesses satisfy $\|w_1\|_\infty,\|w_2\|_\infty\le B$ and fold as $w=w_1+rw_2$ with $r\in\mathcal{C}$, $\|r\|_{\mathrm{op}}\le\gamma$. Then $\|w\|_\infty\le(1+\gamma)B$. Without norm reduction, folding two previously folded witnesses at each of $k$ levels gives the bound $(1+\gamma)^{k}B$, and folding a running witness with fresh witnesses of norm $B$ for $k$ steps gives $(1+k\gamma)B$. Binding of Ajtai commitments, and hence knowledge soundness, holds only for openings of norm below the Module-SIS bound $\beta<q$, so the folded witnesses must stay below $\beta$: with a fixed modulus this allows at most $\log_{1+\gamma}(\beta/B)$ levels of the first kind and $(\beta/B-1)/\gamma$ steps of the second, unless each fold is preceded by a norm-reducing step such as base-$b$ decomposition together with a range proof.

## Proof sketch

Apply $\|w_1+rw_2\|_\infty\le\|w_1\|_\infty+\|r\|_{\mathrm{op}}\|w_2\|_\infty$ inductively. Extraction of earlier witnesses from later ones multiplies by inverses of challenge differences, which can only increase norms, so the bound on the final witness controls soundness.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Proof depends on

- [Relaxed binding of Ajtai commitments with challenge-difference openings](ajtai-relaxed-binding.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", IACR ePrint 2024/257 (2024).
