# Hopkins et al.: SoS distinguishers for noise-robust problems yield spectral distinguishers

Let $\mathcal{I} = A^N$ be a space of instances with a product distribution $\nu$ (null), and let $\mathcal{S} = \{g_j(x, I) = 0\}_{j \in [m]}$ be a polynomial system in program variables $x$, ranging over a solution set $\mathcal{X} \subseteq B^n$, and instance variables $I \in \mathcal{I}$, of degree at most $2d$ in $x$ and at most $k$ in $I$; let $\mu$ (planted) be a distribution over instances on which $\mathcal{S}$ is feasible. For $S \subseteq [N]$ write $I_S$ for the sub-instance on the coordinates in $S$, and let $\Theta$ be a distribution over subsets of $[N]$. Following HKPRSS Definition 2.5, $\mathcal{S}$ is *$\varepsilon$-robustly inferable* for $\mu$ and $\Theta$ if there is a map $x(\cdot)$ from sub-instances to $\mathcal{X}$ with

$$
\Pr_{I \sim \mu,\ S \sim \Theta,\ \tilde I \sim \nu|_{I_S}}\bigl[x(I_S) \text{ is feasible for } \mathcal{S} \text{ on } I_S \circ \tilde I\bigr] \ge 1 - \varepsilon,
$$

where $I_S \circ \tilde I$ keeps the coordinates of $I$ in $S$ and takes the coordinates outside $S$ from a fresh sample $\tilde I$ of $\nu$. Let $B > dk$ be an integer and suppose that

1. $\mathcal{S}$ is $n^{-8B}$-robustly inferable for $\mu$ and $\Theta$;
2. for $I \sim \nu$, with probability at least $1 - n^{-8B}$, $\mathcal{S}$ admits a degree-$d$ sum-of-squares refutation with numbers bounded by $n^{B}$;
3. $D$ is an integer such that $\Pr_{S \sim \Theta}[\alpha \subseteq S] \le n^{-8B}$ for every $\alpha \subseteq [N]$ with $|\alpha| \ge D - 2dk$.

Then there is a matrix polynomial $Q$ of degree $2D$ in the instance, with $Q(I) \in \mathbb{R}^{[n]^{\le d} \times [n]^{\le d}}$, such that

$$
\mathbb{E}_{I \sim \mu}\bigl[\lambda^+_{\max}(Q(I))\bigr] \ge n^{B/2}\, \mathbb{E}_{I \sim \nu}\bigl[\lambda^+_{\max}(Q(I))\bigr] \quad\text{and}\quad \mathbb{E}_{I \sim \mu}\bigl[\lambda^+_{\max}(Q(I))\bigr] > 0,
$$

where $\lambda^+_{\max}$ is the largest non-negative eigenvalue (taken to be $0$ when there is none); HKPRSS state this as a ratio of at least $n^{B/2}$. In words: for noise-robust planted problems, degree-$d$ SoS is no stronger than spectral tests on $n^{O(d)}$-dimensional matrices with low-degree polynomial entries, which covers random CSP refutation, tensor and sparse PCA, densest-$k$-subgraph, community detection and planted clique. This does not say that SoS is no stronger than scalar low-degree polynomial tests, since $\lambda^+_{\max}$ is not itself a low-degree polynomial; that stronger statement is the authors' Conjecture 1.2.

## Proof sketch

Argue by contradiction: assume no degree-$2D$ matrix polynomial distinguishes $\mu$ from $\nu$; then scalar degree-$D$ polynomials have comparable norms under $\mu$ and $\nu$. For each subsampled set $S$, weight the moment matrix of the solution inferred from $I_S$ by the relative density $\mu/\nu$ averaged over completions of $I_S$, and average over $S \sim \Theta$. Robust inference makes the result nearly feasible for the SoS relaxation, and since each term depends only on $I_S$, the average involves only low-degree functions of the instance; the no-distinguisher assumption then transfers its near-feasibility and positivity to null instances. This yields an approximate degree-$d$ pseudo-distribution for $I \sim \nu$, contradicting the SoS refutation.

## Depends on

- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)
- [Low-degree likelihood ratio and low-degree advantage](../../../Probability/statistical-estimation/minimax-lower-bounds/low-degree-likelihood-ratio-method/low-degree-likelihood-ratio.md)

## Sources

- S. B. Hopkins, P. K. Kothari, A. Potechin, P. Raghavendra, T. Schramm, D. Steurer, "The power of sum-of-squares for detecting hidden structures", FOCS (2017), arXiv:1710.05017.
