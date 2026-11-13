# Transfer of functional limit theorems from `C((0,T))` to `D((0,T))` (continuous limit)

Let `X n` be `D([0,T])`-valued processes and `Y n` continuous processes (for instance linear
interpolations of `X n`). Assume
* *tightness*: the laws of `Y n` on `C([0,T])` form a tight family;
* *finite-dimensional convergence*: for every finite set of times `I`, `(Y n t)_{t ∈ I}`
  converges in distribution to `(Z t)_{t ∈ I}`;
* *jump control*: for each `ε > 0`, outside measurable sets of vanishing probability,
  `sup_t |X n t - Y n t| ≤ ε`.

Then `X n → Z` in distribution in the Skorokhod J1 topology on `D([0,T])`.

## Sources

- Billingsley (1999), Theorem 7.5 (tightness + fdd in `C`), Theorem 3.1 (converging together), and the J1-vs-uniform comparison of §12; this is the route used for Donsker's theorem in `D` (Billingsley, Theorem 14.1/16.1). The tightness and fdd hypotheses together amount to `Y n → Z` in distribution in `C`, so this is converging together (Theorem 3.1) plus the `C → D` inclusion. It has no quadratic-variation hypothesis and no martingale structure: the martingale CLT that would produce finite-dimensional convergence and the tightness estimate are inputs. `tendstoInDistribution_skorokhodStepProcess` discharges them for i.i.d. increments.
