# Threshold for increasing paths in regular trees

**Setting (accessibility percolation).** Let $\mathbb T_{n,h}$ be the rooted regular $n$-ary tree of height $h$. Label every non-root vertex with i.i.d. continuous random variables (the House-of-Cards fitness landscape). A root-to-leaf path is *increasing* (selectively accessible) if the labels strictly increase along it. Under strong selection and weak mutation in a haploid asexual population started from a least-fit genotype whose mutants never coincide, the genotype space is such a tree and the feasible evolutionary trajectories are exactly the increasing paths.

**Theorem.** Let $n=\lfloor\alpha h\rfloor$. As $h\to\infty$,

$$
\mathbb P(\text{an increasing path exists})\ \longrightarrow\ \begin{cases}0,&\alpha\le 1/e,\\ 1,&\alpha>1/e.\end{cases}
$$

Moreover, for every $\alpha>1/e$ there are $\delta,\eta>0$ such that, with probability at least $1-e^{-\eta h}$, there are at least $e^{\delta h}$ increasing paths.

**Theorem (critical window).** Let $n=\frac{1+\beta_h}{e}\,h$ with $\beta_h\to0$. Then

$$
\mathbb P(\text{an increasing path exists})\ \longrightarrow\ \begin{cases}0,&\text{if }\log h-2h\beta_h\to\infty,\\ 1,&\text{if }h\beta_h/\log h\to\infty.\end{cases}
$$

## Depends on

- [Accessible mutational paths in the House-of-Cards landscape](../../../population-genetics/selection-migration-and-transmission/fitness-landscapes/accessible-adaptive-paths.md)

## Proof depends on

- [The Paley–Zygmund inequality](../../../../Probability/concentration-inequalities/paley-zygmund.md)

## Expansion

A fixed root-to-leaf path is increasing with probability $1/h!$, and there are $n^h$ paths, so the expected number of increasing paths is $n^h/h!\approx(\alpha e)^h/\sqrt{2\pi h}$: the first moment vanishes for $\alpha<1/e$ (and, with more care, at $\alpha=1/e$), which gives the lower half of the threshold. For $\alpha>1/e$ the proof counts a restricted family $N_\varepsilon$ of "well-spaced" increasing paths whose $j$-th label exceeds $j/(h+1)$ (up to a margin $\varepsilon$), using the identity $\mathbb P(U_1\le\dots\le U_j,\ U_i\ge i/(j+1))=1/(j+1)!$ for uniforms. This gives $\mathbb E N_\varepsilon\ge(\alpha(1-\varepsilon)e)^h/(3h^{3/2})$ and a second moment bound $\mathbb E N_\varepsilon^2\le\mathbb E N_\varepsilon+(\mathbb E N_\varepsilon)^2+c(\alpha(1-\varepsilon)e)^{2h}$, so Paley–Zygmund yields a positive probability. A Chernoff bound on the number of good vertices in the first few generations then boosts this to probability tending to one, since many independent subtrees each get an independent chance. Accessibility on trees with $n\propto h$ thus has a sharp transition at branching ratio $1/e$ per step.

## Sources

- Matthew I. Roberts, Lee Zhuo Zhao, "Increasing paths in regular trees", *Electronic Communications in Probability* 18 (2013), paper 87, 1–10, <https://doi.org/10.1214/ECP.v18-2784>; preprint arXiv:1305.0814 (2013), Theorems 1 and 2, Proposition 3, Lemma 4, Proposition 5, Lemmas 6–7, <https://doi.org/10.48550/arXiv.1305.0814>.
- S. Nowak, J. Krug, "Accessibility percolation on $n$-trees", *EPL* 101 (2013) 66004 (subcritical half, $\alpha\le1/e$).
