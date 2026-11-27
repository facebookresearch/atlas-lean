# L^p seminorms under a probability measure increase with the exponent

Let $\mu$ be a probability measure on a measurable space $\alpha$ and let $f$ be an almost everywhere strongly measurable function on $\alpha$ with values in a space carrying a continuous extended norm $\|\cdot\|_e$ (for instance $\mathbb{R}$ or $\mathbb{C}$). For real exponents $0 < p \le q$,

$$
\Bigl(\int \|f\|_e^{\,p}\, d\mu\Bigr)^{1/p} \le \Bigl(\int \|f\|_e^{\,q}\, d\mu\Bigr)^{1/q},
$$

both sides read in $[0, \infty]$.

For example, for a real function $f$ on a nonempty finite set under the uniform distribution, every function is measurable and the inequality reads $\|f\|_p \le \|f\|_q$ with $\|f\|_p = (\mathbb{E}|f|^p)^{1/p}$, all these norms being finite; the Boolean cube $\{-1,1\}^n$ is the main case used in the analysis of Boolean functions.

## Sources

- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842: [MeasureTheory.eLpNorm'_le_eLpNorm'_of_exponent_le](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean#L105 "MeasureTheory.eLpNorm'_le_eLpNorm'_of_exponent_le").
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
