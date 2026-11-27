# Relaxed binding of Ajtai commitments with challenge-difference openings

Let $A\in R_q^{\kappa\times m}$ be uniform and $\mathsf{Com}(w)=Aw$ for $w\in R_q^{m}$. Call $(w,c)$ with $c$ a difference of two distinct elements of a strong sampling set $\mathcal{C}$ a *relaxed opening* of $C$ with norm bound $B$ if $Aw=cC$ and $\|w\|_\infty< B$. If an efficient adversary outputs $C$ and two relaxed openings $(w,c)$, $(w',c')$ with $c'w\ne cw'$, then $c'w-cw'$ is a nonzero vector with $A(c'w-cw')=0$ and $\|c'w-cw'\|_\infty<2B\max_{c\in\mathcal{C}-\mathcal{C}}\|c\|_{\mathrm{op}}$, i.e., a solution to Module-SIS. Hence relaxed binding holds under the Module-SIS assumption with norm bound $\beta=2B\max\|c\|_{\mathrm{op}}$.

## Proof sketch

Multiply $Aw=cC$ by $c'$ and $Aw'=c'C$ by $c$ and subtract. The norm bound follows from the triangle inequality and the definition of operator norm.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", ASIACRYPT (2025), IACR ePrint 2024/257.
- Dan Boneh, Binyi Chen, "LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems", CRYPTO (2025), IACR ePrint 2025/247.
