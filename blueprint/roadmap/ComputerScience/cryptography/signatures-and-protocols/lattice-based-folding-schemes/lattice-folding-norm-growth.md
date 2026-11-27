# Worst-case norm bounds for folding lattice witnesses without norm reduction

Let witnesses satisfy $\|w_1\|_\infty,\|w_2\|_\infty\le B$ and fold as $w=w_1+rw_2$ with $r\in\mathcal{C}$, $\|r\|_{\mathrm{op}}\le\gamma$. Then $\|w\|_\infty\le(1+\gamma)B$. Without norm reduction, folding two previously folded witnesses at each of $k$ levels keeps the norm at most $(1+\gamma)^{k}B$, and folding a running witness with fresh witnesses of norm at most $B$ for $k$ steps keeps it at most $(1+k\gamma)B$. Ajtai commitments are binding, under Module-SIS, only for openings whose norm is below a bound $\beta$ fixed by the parameters, so these inequalities give a sufficient condition: if $(1+\gamma)^{k}B<\beta$, respectively $(1+k\gamma)B<\beta$, every folded witness is guaranteed to stay in the binding range for that many levels or steps. They are worst-case upper bounds, not limits on how far folding can actually go: the norms reached can be much smaller (folding zero witnesses never increases the norm), but beyond these budgets no norm guarantee follows from the folding alone. This is why LatticeFold precedes each fold by a base-$b$ decomposition of the witnesses together with a range proof, keeping the folded witness below the same bound at every step.

## Proof sketch

Apply $\|w_1+rw_2\|_\infty\le\|w_1\|_\infty+\|r\|_{\mathrm{op}}\|w_2\|_\infty$ inductively. Separately, extraction of earlier witnesses from later ones multiplies by inverses of challenge differences, whose norms can be large, so a norm bound on the final witness alone does not bound the extracted witnesses; this is why LatticeFold proves the range of the inputs directly.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Proof depends on

- [Relaxed binding of Ajtai commitments with challenge-difference openings](ajtai-relaxed-binding.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", ASIACRYPT (2025), IACR ePrint 2024/257, Section 1 (contributions).
