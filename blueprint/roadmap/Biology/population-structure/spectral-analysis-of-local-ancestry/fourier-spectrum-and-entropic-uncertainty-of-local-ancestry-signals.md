# Fourier spectrum and entropic uncertainty of local ancestry signals

**Representations.** On a genomic interval $[0,L]$, let $p(l) = (p_1(l),\dots,p_K(l))$ be the probabilities that position $l$ descends from each of $K$ reference populations, $\sum_k p_k(l) = 1$. The *spherical representation* is

$$y(l) = \big(\sqrt{p_1(l)},\dots,\sqrt{p_K(l)}\big)^{\mathsf T},$$

a point on the unit sphere of $\mathbb{R}^K$, and the ancestry correlation between two positions is the Bhattacharyya coefficient $A(l_1,l_2) = y(l_1)^{\mathsf T} y(l_2) \in [0,1]$, with $A(l,l) = 1$. For $K = 2$ the *complex representation* is $z(l) = \sqrt{p_1(l)} + i\sqrt{p_2(l)}$ with $A(l_1,l_2) = z(l_1)\overline{z(l_2)}$, whose real part is the Bhattacharyya coefficient. The *hybrid index* is $h_k = \frac1L\int_0^L p_k(l)\,dl$.

**Mean autocorrelation (Theorem 1).**

$$a := \frac{1}{L^2}\iint_{[0,L]^2} A(l_1,l_2)\,dl_1\,dl_2 = \Big\|\frac1L\int_0^L y(l)\,dl\Big\|^2 = \Big|\frac1L\int_0^L z(l)\,dl\Big|^2 .$$

**Folded Fourier spectrum.** Expand $y_k(l) = \sum_{n\in\mathbb{Z}} \hat y_{k,n}\, e^{i 2\pi n l/L}$ and set $\zeta_0 = \sum_k |\hat y_{k,0}|^2$, $\zeta_n = 2\sum_k |\hat y_{k,n}|^2$ for $n \ge 1$. By Parseval, $\sum_n \zeta_n = \frac1L\int_0^L \sum_k p_k(l)\,dl = 1$, so $\{\zeta_n\}$ is a probability distribution over frequencies. For $K = 2$ the spectrum computed from $z$ (with $\zeta_n = |Z_n|^2 + |Z_{-n}|^2$ for $n \ge 1$) coincides with that of $y$ (Theorem 2). The *within-individual entropy* is $S_w = -\sum_n \zeta_n \ln \zeta_n$.

**Entropic uncertainty (Theorem 3).** Let $A(l) = \frac1L\int_0^L y(x)^{\mathsf T} y(x+l)\,dx$ (with $y$ extended $L$-periodically) and $Q = \int_0^L A(l)^2\,dl$. Then

$$S_w \ \ge\ \int_0^L \frac{A(l)^2}{Q}\ln\frac{A(l)^2}{Q}\,dl + \Big(\frac1L\int_0^L A(l)\,dl - 1\Big)\ln 2 + \ln L .$$

The right-hand side is invariant under rescaling the interval; after rescaling $A$ to $[0,2]$ it reads $S_w \ge -S(A^2) + a\ln 2$, where $S(A^2)$ is the differential entropy of the normalized density $A^2/Q$.

## Depends on

- [Parseval's identity on the circle](../../../Analysis/harmonic-analysis/fourier-series/convergence-of-fourier-series/parseval-identity-on-the-circle.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

Theorem 1 is the identity $\|\int y\|^2 = \iint y(l_1)^{\mathsf T}y(l_2)$: the norm of the averaged spherical signal measures how similar ancestries are across the interval, not the mean ancestry itself (which is the hybrid index). The Wiener–Khinchin relation gives $A(l) = \sum_n \eta_n e^{i2\pi nl/L}$ with $\eta_n = \sum_k |\hat y_{k,n}|^2$, so the spectrum and the autocorrelation form a Fourier pair; long unbroken ancestry tracts concentrate $\{\zeta_n\}$ at low frequencies (small $S_w$), while fine-scale mosaics spread it out. The inequality follows by applying an entropic uncertainty relation between a sequence and its Fourier transform to the pair $(\eta_n, A)$, a majorization step comparing $\{\eta_n\}$ with $\{\eta_n^2\}$, and folding $\eta_{\pm n}$ into $\zeta_n$.

## Sources

- T. Xiong, X. Li, M. Yago, J. Mallet, "Admixture of evolutionary rates across a butterfly hybrid zone", eLife 11 (2022) e78135, Methods (Definitions 1–9, Equations (25)–(37), Theorems 1–3), <https://doi.org/10.7554/eLife.78135>, PMCID PMC9246367.
