# Miner's rule for variable-amplitude fatigue

Let a material have a fatigue life curve, the *S–N curve*, assigning to each stress amplitude $S$ in its range a number of cycles to failure $N(S) > 0$ under constant-amplitude loading. A variable-amplitude load history is summarized by blocks: $n_j$ cycles at amplitude $S_j$, for $j = 1, \dots, k$.

**Definition (Palmgren–Miner rule).** The *damage* of the history is
$$
D = \sum_{j=1}^{k} \frac{n_j}{N(S_j)},
$$
and the rule predicts failure when $D$ reaches $1$.

**Consequences.**
1. *Remaining life.* After $n_1$ cycles at $S_1$ with $n_1 < N(S_1)$, the rule predicts $n_2 = N(S_2)\,(1 - n_1/N(S_1))$ further cycles at $S_2$.
2. *Order independence.* $D$ depends only on the multiset of blocks, not on their order. So the rule cannot represent load-sequence effects.
3. *Equivalent amplitude.* If $N(S) = C S^{-b}$ with $C, b > 0$, a history of $n = \sum_j n_j$ cycles has the same damage as $n$ cycles at the constant amplitude
$$
S_{\mathrm{eq}} = \Bigl(\frac{1}{n}\sum_j n_j S_j^{\,b}\Bigr)^{1/b}.
$$

**Proof.**
1. Solve $n_1/N(S_1) + n_2/N(S_2) = 1$ for $n_2$.
2. A finite sum is invariant under permutation.
3. $D = C^{-1}\sum_j n_j S_j^{\,b}$, which equals $n\,S_{\mathrm{eq}}^{\,b}/C = n/N(S_{\mathrm{eq}})$.

Miner's rule is an empirical model, not a consequence of mechanics: damage accumulation in fatigue is generally nonlinear and depends on the load sequence. Applying the rule to an irregular history also requires a cycle-counting method, such as rainflow counting, and a mean-stress correction. Creep at high temperature requires separate constitutive laws.

## Background

- [Griffith energy balance for brittle fracture](griffith-energy-balance-for-brittle-fracture.md)

## Sources

- D. Roylance, *Fatigue*, course module, Department of Materials Science and Engineering, MIT, 2001, <http://web.mit.edu/course/3/3.11/www/modules/fatigue.pdf>:
    - $S$–$N$ curves, the endurance limit and the Goodman diagram;
    - "Miner's law for cumulative damage": $n_1/N_1 + n_2/N_2 = 1$, the remaining life $n_2 = N_2(1 - n_1/N_1)$, the general form $\sum n_j/N_j = 1$ (Eq. 1), Example 1, and the caveat that linear damage accumulation should be viewed skeptically. Order independence and the power-law equivalent amplitude are derived here.
