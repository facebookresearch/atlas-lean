# Elimination probability under a renewal model with gamma posterior

**Renewal model.** Let $I_s$ be daily incidence, $w_u$ the serial-interval (generation-time) probabilities, and $\Lambda_s = \sum_{u=1}^{s-1} I_{s-u} w_u$ the total infectiousness. Then $I_s \mid I_1^{s-1} \sim \mathrm{Poisson}(R_{s-1}\Lambda_s)$. Assuming the reproduction number is constant, $R_{\tau(s)}$, over a look-back window $\tau(s) = \{s-k+1, \dots, s\}$ and placing a $\mathrm{Gam}(a, 1/c)$ (shape–scale) prior on it gives the conjugate posterior

$$R_{\tau(s)} \mid I_1^s \sim \mathrm{Gam}\Big(\alpha_{\tau(s)} = a + \sum_{u \in \tau(s)} I_u,\ \ \beta_{\tau(s)} = \frac{1}{c + \sum_{u\in\tau(s)}\Lambda_u}\Big),$$

with mean $\hat R_{\tau(s)} = \alpha_{\tau(s)}\beta_{\tau(s)}$, and the one-step posterior predictive is negative binomial, $I_{s+1} \mid I_1^s \sim \mathrm{NB}\big(\alpha_{\tau(s)},\ p = \Lambda_{s+1}\beta_{\tau(s)}/(1 + \Lambda_{s+1}\beta_{\tau(s)})\big)$, with mean $\hat I_{s+1} = \Lambda_{s+1}\hat R_{\tau(s)}$.

**Theorem.** The estimated probability that the epidemic is over at time $s$, $z_s = \Pr\big(I_{s+1} = I_{s+2} = \cdots = 0 \mid I_1^s\big)$, equals

$$z_s = \prod_{j=s}^{\infty} \Big( 1 + \frac{\hat I_{j+1}}{\alpha_{\tau(j)}} \Big)^{-\alpha_{\tau(j)}},$$

where for $j > s$ the quantities $\alpha_{\tau(j)}$, $\beta_{\tau(j)}$, $\Lambda_{j+1}$ and $\hat I_{j+1} = \Lambda_{j+1}\alpha_{\tau(j)}\beta_{\tau(j)}$ are computed from the observed curve $I_1^s$ extended by zeros $I_{s+1} = \cdots = I_j = 0$. An outbreak is declared over with confidence $\mu\%$ at the stopping time $t_\mu = \min\{ s : z_s \ge \mu/100 \}$.

## Expansion

By the chain rule of probability, $z_s = \Pr(I_{s+1} = 0 \mid I_1^s)\prod_{j > s}\Pr(I_{j+1} = 0 \mid I_1^j)$, where each later factor conditions on the observed data followed by the hypothesized zeros (pseudo-data). Integrating the Poisson likelihood against the gamma posterior gives the negative binomial predictive, whose mass at zero is $(1 - p)^{\alpha} = (1 + \Lambda_{j+1}\beta_{\tau(j)})^{-\alpha_{\tau(j)}} = (1 + \hat I_{j+1}/\alpha_{\tau(j)})^{-\alpha_{\tau(j)}}$. Each factor lies in $(0, 1]$ and tends to $1$ as the infectiousness $\Lambda_{j+1}$ of the zero-extended curve decays, so the product converges when the serial interval has finite support or light tails. The formula embeds uncertainty in $R$ through the shape $\alpha$: with $\hat I$ fixed, larger $\alpha$ (more data) moves each factor toward the Poisson value $e^{-\hat I}$. If true cases are reported with probability $\rho_s < 1$, the observed curve understates $\Lambda$ and $\hat I$ and so inflates $z_s$, causing premature declarations; counting imported cases as local inflates the window counts entering $\alpha$ and $\hat R$, lowering $z_s$ and delaying declarations.

## Sources

- K. V. Parag, C. A. Donnelly, R. Jha and R. N. Thompson, "An exact method for quantifying the reliability of end-of-epidemic declarations in real time", PLoS Computational Biology 16 (2020), e1008478, Methods (Eqs. (1)–(2)) and Results (Eqs. (5)–(7), Theorem 1), <https://doi.org/10.1371/journal.pcbi.1008478>, PMCID: PMC7717584.
