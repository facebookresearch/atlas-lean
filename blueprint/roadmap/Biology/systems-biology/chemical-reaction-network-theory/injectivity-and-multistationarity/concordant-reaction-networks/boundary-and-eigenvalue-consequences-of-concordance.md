# Boundary, eigenvalue and instability consequences of concordance and discordance

**Setting.** Reaction networks, concordance and weakly monotonic kinetics are as in the injectivity characterization listed under Depends on. A network is *weakly reversible* if every reaction lies on a directed cycle of the reaction graph, *conservative* if $S^\perp$ contains a strictly positive vector, and *normal* if there are $q \in \mathbb{R}^{\mathscr{S}}_{>0}$ and $\eta \in \mathbb{R}^{\mathscr{R}}_{>0}$ such that $\sigma \mapsto \sum_{y\to y'} \eta_{y\to y'}\big(\sum_s q_s y_s \sigma_s\big)(y'-y)$ is nonsingular on $S$ (every weakly reversible network is normal). Its *fully open extension* adds the inflow and outflow reactions $0 \rightleftarrows s$ for every species $s$. The kinetics is *differentiably monotonic* at $c^*$ if each rate is differentiable there with $\partial \mathscr{K}_{y\to y'}/\partial c_s > 0$ for $s \in \operatorname{supp} y$ and $=0$ otherwise.

**Theorem (boundary behavior and existence).** Let the network be weakly reversible and concordant.

1. No composition on the boundary of a nontrivial stoichiometric compatibility class is an equilibrium; at each such composition some absent species is produced at strictly positive rate.
2. If moreover the network is conservative and the kinetics is continuous, each nontrivial stoichiometric compatibility class contains a positive equilibrium; if the kinetics is also weakly monotonic, that equilibrium is the only equilibrium in the class.

**Theorem (eigenvalues).** Let the kinetics be differentiably monotonic at a positive $c^*$ and $df(c^*) : S \to S$ the derivative of the species formation rate.

1. If the network is concordant, $df(c^*)$ is nonsingular.
2. If the fully open extension is concordant, $df(c^*)$ has no positive real eigenvalue; if moreover the network is normal (e.g. weakly reversible), every real eigenvalue of $df(c^*)$ is negative.
3. A normal network is concordant whenever its fully open extension is concordant.

**Theorem (discordance).** Let the network have positively dependent reaction vectors (true for weakly reversible networks).

1. If it is discordant, some differentiably monotonic kinetics gives a positive degenerate equilibrium.
2. If its fully open extension is discordant, some differentiably monotonic kinetics gives an unstable positive equilibrium. In particular every weakly reversible discordant network admits a differentiably monotonic kinetics with a positive unstable equilibrium.

## Depends on

- [Concordance characterizes injectivity under all weakly monotonic kinetics](concordance-characterizes-injectivity-under-weakly-monotonic-kinetics.md)
- [Weakly reversible reaction network](../../../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)

## Expansion

Concordance excludes sign-compatible pairs $(\alpha,\sigma)$ with $L\alpha = 0$; at a differentiably monotonic composition $df(c^*)\sigma = L\alpha$ with $\alpha$ the induced rate changes, so a kernel vector of $df(c^*)$ would be a discordance witness. Positive real eigenvalues $\lambda$ correspond to $df(c^*)\sigma = \lambda\sigma$, which can be absorbed into the outflow reactions of the fully open extension, giving the eigenvalue statement. On the boundary, weak reversibility plus concordance rules out "reaction-transitive" boundary compositions, so absent species are always replenished; combined with a Brouwer fixed-point argument on compact compatibility classes of a conservative network this yields existence, and injectivity yields uniqueness.

## Sources

- Guy Shinar and Martin Feinberg, "Concordant chemical reaction networks", Mathematical Biosciences 240 (2012), 92–113, <https://doi.org/10.1016/j.mbs.2012.05.004>; numbering as in arXiv:1109.2923: Theorem 6.3, Corollary 6.4 and Theorem 6.7 (Section 6), Definition 7.2, Theorems 7.4, 7.6 and Corollary 7.7 (Section 7), Theorem 8.1 and Corollaries 8.2–8.3 (Section 8).
