# Concordance characterizes injectivity under all weakly monotonic kinetics

**Setting.** A reaction network $\{\mathscr{S},\mathscr{C},\mathscr{R}\}$ has species $\mathscr{S}$, complexes $y \in \mathbb{R}^{\mathscr{S}}_{\ge 0}$ and reactions $y \to y'$; its stoichiometric subspace is $S = \operatorname{span}\{y'-y\}$. Let $L : \mathbb{R}^{\mathscr{R}} \to S$, $L\alpha = \sum_{y \to y'} \alpha_{y \to y'}(y'-y)$.

**Definition (concordance).** The network is *concordant* if there do **not** exist $\alpha \in \ker L$ and a nonzero $\sigma \in S$ such that

1. for each reaction $y \to y'$ with $\alpha_{y\to y'} \neq 0$, $\operatorname{supp} y$ contains a species $s$ with $\operatorname{sgn}\sigma_s = \operatorname{sgn}\alpha_{y\to y'}$;
2. for each reaction $y \to y'$ with $\alpha_{y\to y'} = 0$, either $\sigma_s = 0$ for all $s \in \operatorname{supp} y$, or $\operatorname{supp} y$ contains species $s, s'$ with $\operatorname{sgn}\sigma_s = -\operatorname{sgn}\sigma_{s'} \neq 0$.

Otherwise it is *discordant*.

**Kinetics.** A kinetics assigns to each reaction a rate function $\mathscr{K}_{y\to y'} : \mathbb{R}^{\mathscr{S}}_{\ge 0} \to \mathbb{R}_{\ge 0}$, positive exactly when all reactant species are present; the species formation rate is $f(c) = \sum \mathscr{K}_{y\to y'}(c)(y'-y)$. The kinetics is *weakly monotonic* if for compositions $c, c^*$ and every reaction $y \to y'$ with $\operatorname{supp} y \subseteq \operatorname{supp} c \cap \operatorname{supp} c^*$: $\mathscr{K}_{y\to y'}(c^*) > \mathscr{K}_{y\to y'}(c)$ implies $c^*_s > c_s$ for some $s \in \operatorname{supp} y$; and $\mathscr{K}_{y\to y'}(c^*) = \mathscr{K}_{y\to y'}(c)$ implies either $c^*_s = c_s$ for all $s \in \operatorname{supp} y$ or there are $s, s' \in \operatorname{supp} y$ with $c^*_s > c_s$ and $c^*_{s'} < c_{s'}$. Mass-action kinetics is weakly monotonic. The kinetic system is *injective* if $f(c^*) \neq f(c)$ for distinct stoichiometrically compatible $c, c^*$ ($c^* - c \in S$) with at least one of them positive.

**Theorem.**

1. If the network is concordant, every weakly monotonic kinetic system on it is injective; in particular it cannot admit two distinct stoichiometrically compatible equilibria at least one of which is positive.
2. If the network is discordant, some weakly monotonic kinetics makes it non-injective.

Hence a network has injectivity under all weakly monotonic kinetics if and only if it is concordant.

## Expansion

If $f(c^*) = f(c)$ with $\sigma = c^* - c \in S \setminus \{0\}$, set $\alpha_{y\to y'} = \mathscr{K}_{y\to y'}(c^*) - \mathscr{K}_{y\to y'}(c)$; then $L\alpha = f(c^*) - f(c) = 0$, and weak monotonicity forces exactly the sign conditions 1–2 between $\alpha$ and $\sigma$, contradicting concordance. Conversely, a discordance witness $(\alpha,\sigma)$ is realized by constructing rate functions whose differences along $\sigma$ equal $\alpha$ while remaining weakly monotonic. Concordance is a purely sign-pattern condition on the network, so it can be decided combinatorially without reference to rate constants.

## Sources

- Guy Shinar and Martin Feinberg, "Concordant chemical reaction networks", Mathematical Biosciences 240 (2012), 92–113, <https://doi.org/10.1016/j.mbs.2012.05.004>; numbering as in arXiv:1109.2923: Definition 4.1, Propositions 4.8–4.9 and Theorem 4.11 (Section 4), Proposition 9.6 (Section 9).
