# Poisson-mixture limit of the chemical master equation under slow promoter kinetics

**Setting.** A gene regulatory network has $N$ genes whose promoters jointly take $L$ configurations $d \in \{0, \dots, L-1\}$ (each promoter bound or unbound by transcription-factor multimers), protein copy numbers $X_i$, and multimers $X_{ic}$ formed by $n_i X_i \rightleftharpoons X_{ic}$ (rates $\beta_i$, $\beta_{-i}$). Given configuration $d$ (component $d_i$ for gene $i$), protein $i$ is produced at rate $k_{i d_i}$ and degraded at rate $k_{-i}$ per molecule. Promoter binding and unbinding reactions are slow: their propensities carry a factor $\varepsilon > 0$. Ordering states by promoter configuration, the chemical master equation reads

$$\dot p(t) = \big(\tilde\Lambda + \varepsilon\hat\Lambda\big)\, p(t), \qquad \tilde\Lambda = \operatorname{diag}(\Lambda_0, \dots, \Lambda_{L-1}),$$

where $\Lambda_d$ generates the protein dynamics with the promoter frozen at $d$ (fast part) and $\hat\Lambda$ collects the promoter transitions (slow part).

**Conditional stationary laws.** With the promoter frozen at $d$, the proteins are independent birth–death processes and the stationary law of the non-multimerized proteins is the product Poisson distribution

$$\pi_{X\mid d}(x) = \prod_{i=1}^N \frac{\lambda_{i d_i}^{x_i}}{x_i!}e^{-\lambda_{i d_i}}, \qquad \lambda_{i d_i} = \frac{k_{i d_i}}{k_{-i}},$$

and the multimer count $X_{ic}$ is independently Poisson with mean $\dfrac{\beta_i}{n_i!\,\beta_{-i}}\Big(\dfrac{k_{id_i}}{k_{-i}}\Big)^{n_i}$.

**Theorem.** As $\varepsilon \to 0^+$, the stationary distribution of the protein process converges to the mixture

$$\pi(x) = \sum_{d=0}^{L-1} \lambda_d\, \pi_{X\mid d}(x),$$

where the weights $\lambda = (\lambda_0, \dots, \lambda_{L-1})$ form the stationary distribution of the reduced $L$-state Markov chain whose generator $\Lambda_r$ is $\hat\Lambda$ averaged against the conditional stationary laws. Concretely, a binding reaction $TF + D^i_{d_i} \xrightarrow{\ \alpha\ } D^i_{d_i'}$ becomes the promoter transition $D^i_{d_i} \to D^i_{d_i'}$ at rate $\alpha\, \mathbb{E}[TF \mid D = d]$, with the conditional mean multimer count above.

## Depends on

- [Non-explosivity of complex-balanced stochastic reaction networks](../../part-01/stochastic-reaction-networks/non-explosivity-of-complex-balanced-stochastic-reaction-networks.md)

## Expansion

At $\varepsilon = 0$ the generator is block diagonal, so the kernel is spanned by the extended conditional laws $\bar\pi_{X\mid d}$, each supported on configuration $d$. Inserting $\bar\pi^\varepsilon = \bar\pi^{(0)} + \varepsilon\,\bar\pi^{(1)} + o(\varepsilon)$ into $(\tilde\Lambda + \varepsilon\hat\Lambda)\bar\pi^\varepsilon = 0$ gives $\tilde\Lambda\bar\pi^{(0)} = 0$, hence $\bar\pi^{(0)} = \sum_d \lambda_d \bar\pi_{X\mid d}$, and at first order $\tilde\Lambda\bar\pi^{(1)} + \hat\Lambda\bar\pi^{(0)} = 0$. Summing within each block annihilates $\tilde\Lambda$ (its blocks are conservative generators), leaving $\Lambda_r\lambda = 0$ with $\Lambda_r = \operatorname{diag}(\mathbf 1^\top, \dots, \mathbf 1^\top)\,\hat\Lambda\,[\bar\pi_{X\mid 0} \cdots \bar\pi_{X\mid L-1}]$, which is the reduced chain. Each promoter configuration thus contributes one Poisson "mode" centred at its production-to-decay ratios, so a network can have as many modes as promoter configurations, more than the stable equilibria of the corresponding deterministic model (for example a noncooperative self-activating gene or toggle switch can be multimodal); cooperativity enters only through the weights, via $\mathbb{E}[TF \mid d] \propto (k_{id}/k_{-i})^{n_i}$. Distinct mixture components need not produce distinct local maxima when their means are close.

## Sources

- M. A. Al-Radhawi, D. Del Vecchio and E. D. Sontag, "Multi-modality in gene regulatory networks with slow promoter kinetics", PLoS Computational Biology 15 (2019), e1006784, Results (Propositions 1–2, Eqs. (2)–(12), Theorem 3, Corollary 4), <https://doi.org/10.1371/journal.pcbi.1006784>, PMCID: PMC6396950.
