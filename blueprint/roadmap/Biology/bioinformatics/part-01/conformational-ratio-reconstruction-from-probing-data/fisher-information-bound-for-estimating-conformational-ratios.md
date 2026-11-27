# Fisher-information bound for estimating conformational ratios from SHAPE data

**Statement.** Model the SHAPE reactivity at a position that is unpaired in a proportion $p$ of the structures and center-paired in the rest as the weighted sum $X=pX_1+(1-p)X_2$ of independent $X_1\sim f_{\mathrm{un}}$ and $X_2\sim f_{\mathrm{pair}}$, where $f_{\mathrm{un}}$ is the exponential density with rate $\lambda=1.46797$ and $f_{\mathrm{pair}}$ is the generalized extreme value density with shape $\xi=0.762581$, scale $\sigma=0.0492536$ and location $\mu=0.0395857$ (the empirical SHAPE laws the source takes from its reference [19]). Let $g(x,p)$ be the density of $X$, the weighted convolution

$$
g(x,p)=\int\frac{1}{p(1-p)}\,f_{\mathrm{un}}\Big(\frac yp\Big)\,f_{\mathrm{pair}}\Big(\frac{x-y}{1-p}\Big)\,dy,
$$

and $I(p)=\int\big(\partial_p\log g(x,p)\big)^2g(x,p)\,dx$ its Fisher information about $p$ (the source's (7)). Consider $n$ independent such reactivities from an equal mixture ($p=1/2$) of two structures such that at each position one structure is center-paired and the other unpaired. Numerically $I(1/2)\approx2.15$, and every unbiased estimator $\hat p$ of the conformational ratio satisfies

$$
\operatorname{Var}(\hat p)\ge\frac{1}{2.15\,n}.
$$

More generally, if $n$ is the number of positions at which the two structural modes differ in pairing status, the variance of any unbiased estimator of $p$ decreases at most linearly in $n$.

## Expansion

The reactivities are independent, so the Fisher information about $p$ is additive across positions, $I_n(p)=nI(p)$. Differentiating $g(x,p)$ under the integral sign and integrating numerically at $p=1/2$ gives $I(1/2)\approx2.15$ per position (the source's Fig. 5 and the text after it), and the Cramér–Rao inequality $\operatorname{Var}(\hat p)\ge1/I_n(p)$ yields the bound. A model in which each reactivity is instead a draw from the two-component mixture $pf_{\mathrm{un}}+(1-p)f_{\mathrm{pair}}$ is a different one, with smaller information (about $1.54$ at $p=1/2$). Positions where both structures agree carry no information about $p$. The result quantifies an intrinsic limit: the overlap of paired and unpaired reactivity distributions caps how precisely probing data can pin down a mixture weight, independent of the folding algorithm.

## Proof depends on

- [Cramér–Rao inequality with minimal hypotheses](../../../../Probability/statistical-estimation/fisher-information-and-the-cram-r-rao-bound/cramer-rao-general.md)

## Sources

- Torin Greenwood, Christine E. Heitsch, "Deconvolving RNA Base Pairing Signals", arXiv:1801.03055: Section 5 (information content in auxiliary data): Lemma 4 and Conclusion 2 of the Introduction. <https://doi.org/10.48550/arXiv.1801.03055>
