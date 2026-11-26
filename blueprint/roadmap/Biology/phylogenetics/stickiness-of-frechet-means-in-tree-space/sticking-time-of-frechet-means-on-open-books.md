# Sticking time of Fréchet means on open books

**Setting.** The open book $\mathcal B_{K,m}$ consists of $K$ closed half-spaces (pages) $\mathcal P_j=\{(j,v):v\in\mathbb R^m,\ v_1\ge0\}$ glued along their common boundary, the spine $\mathcal S=\{v_1=0\}$, with the induced geodesic metric; neighborhoods of codimension-one strata of BHV tree space have this form, with $K=3$ for a trifurcation. Let $Y_1,Y_2,\dots$ be i.i.d. from $\mu$ on $\mathcal B_{K,m}$ with finite first moment, and $F_n=\arg\min_x\frac1n\sum_{i\le n}d^2(x,Y_i)$ the sample Fréchet mean, which exists, is unique and converges a.s. to the population mean (Sturm). The $j$th folding map $\Phi_j:\mathcal B_{K,m}\to\mathbb R^m$ is the identity on page $j$ and the reflection $R:v_1\mapsto-v_1$ on the other pages. Stickiness, $F_n\in\mathcal S$ for all large $n$ a.s., holds iff
$$\max_{1\le j\le K}\mathbb E_\mu\big[(\Phi_j(Y))_1\big]<0.\tag{S}$$

**Representation lemma (Section 3.2).** Let $S_{j,n}=\sum_{i=1}^n(\Phi_j(Y_i))_1$ be the $j$th folded random walk and $\sigma_j=\sup\{n\ge0:S_{j,n}>0\}$ its last-passage time above $0$. Then $\{F_n\in\mathcal P_j\setminus\mathcal S\}=\{S_{j,n}>0\}$, and the sticking time $T=\inf\{n:F_m\in\mathcal S\ \forall m\ge n\}$ satisfies
$$T=\max_{1\le j\le K}\sigma_j+1\quad\text{a.s.}$$

**Theorem 3.4 (tail of the sticking time).** Assume (S), Cramér's condition (each step law $\nu_j$ of $(\Phi_j(Y))_1$ has $\theta_j>0$ with $\mathbb E e^{\theta_j(\Phi_j(Y))_1}=1$) and a non-lattice condition. Let $\Lambda_j$ be the log-moment generating function of $\nu_j$, minimized at $\gamma_j$, $\alpha=\min_j(-\Lambda_j(\gamma_j))$ and $\mathcal J=\{j:-\Lambda_j(\gamma_j)=\alpha\}$. Then, as $n\to\infty$,
$$\frac{\max_{j\in\mathcal J}c_j}{\sqrt n}(1+o(1))e^{-\alpha n}\le\mathbb P_\mu(T>n)\le\frac{\sum_{j\in\mathcal J}(c_j+C_j)}{\sqrt n}(1+o(1))e^{-\alpha n},$$
with explicit Bahadur–Rao constants $c_j,C_j$.

**Proposition 3.8.** A nonparametric plug-in estimator of the probability that the sample mean leaves the spine in the future, given $Y_1,\dots,Y_n$, is consistent on the logarithmic scale under (S), a double moment condition and the non-lattice condition.

## Expansion

The first-order optimality conditions for the Fréchet mean on an open book, taken from earlier work on sticky open books, say that $F_n$ lies in the interior of page $j$ exactly when the folded empirical mean has positive first coordinate, so $F_n$ leaves the spine iff some folded walk is positive; the sticking time is then the last such $n$. Under (S) every folded walk has negative drift and a finite last-passage time. The lower tail bound uses $\{T>n\}\supseteq\{S_{j,n}>0\}$ and the Bahadur–Rao refinement of Cramér's theorem; the upper bound adds, via the Markov property and an exponential change of measure at the Cramér root $\theta_j$, the probability that a walk currently below zero later returns above it. The estimator applies the same formula with empirical step distributions, and was used to assess the trifurcation among primates, glires and tree shrews.

## Sources

- A. Q. Jaffe, "Phylogenetic Inference and the Stickiness of Fréchet Means, via Precise Asymptotics of an Embedded Random Walk", arXiv preprint (2026), representation lemma of Section 3.2, Theorem 3.4 and Proposition 3.8, <https://doi.org/10.48550/arXiv.2609.24816>.
