# Fisher-information bound for estimating conformational ratios from SHAPE data

**Statement.** Consider $n$ simulated SHAPE reactivities from an equal mixture ($p=1/2$) of two RNA structures such that at each position one structure is center-paired and the other unpaired, with reactivities drawn from the empirical paired and unpaired SHAPE distributions. Then every unbiased estimator $\hat p$ of the conformational ratio satisfies

$$
\operatorname{Var}(\hat p)\ge\frac{1}{2.15\,n}.
$$

More generally, if $n$ is the number of positions at which the two structural modes differ in pairing status, the variance of any unbiased estimator of $p$ decreases at most linearly in $n$.

## Expansion

Each reactivity is an independent draw from the mixture density $p f_{\mathrm u}+(1-p)f_{\mathrm p}$ (or its mirror), so the Fisher information about $p$ is additive across positions, $I_n(p)=n\int\frac{(f_{\mathrm u}-f_{\mathrm p})^2}{pf_{\mathrm u}+(1-p)f_{\mathrm p}}$. Evaluating the integral numerically at $p=1/2$ for the empirical SHAPE distributions gives about $2.15$ per position, and the Cramér–Rao inequality $\operatorname{Var}(\hat p)\ge1/I_n(p)$ yields the bound. Positions where both structures agree carry no information about $p$. The result quantifies an intrinsic limit: the overlap of paired and unpaired reactivity distributions caps how precisely probing data can pin down a mixture weight, independent of the folding algorithm.

## Proof depends on

- [Cramér–Rao inequality with minimal hypotheses](../../../../Probability/statistical-estimation/fisher-information-and-the-cram-r-rao-bound/cramer-rao-general.md)

## Sources

- Torin Greenwood, Christine E. Heitsch, "Deconvolving RNA Base Pairing Signals", arXiv:1801.03055: Section 5 (information content in auxiliary data): Lemma 4 and Conclusion 2 of the Introduction. <https://doi.org/10.48550/arXiv.1801.03055>
