# GTaS model and its marginal Poisson structure

**Model.** Fix $N \ge 1$ neurons indexed by $\mathbb{D} = \{1,\dots,N\}$, a rate $\lambda > 0$, a probability distribution $(p_D)_{D \subseteq \mathbb{D}}$ on markings, and for each marking $D$ a shift (jitter) distribution $Q_D$ on $\mathbb{R}^N$. A realization of the counting process $X = (X_1,\dots,X_N)$ is generated as follows:

1. Draw the event times $\{t_j\}$ of a homogeneous Poisson process of rate $\lambda$ on $\mathbb{R}$ (the mother process).
2. Independently for each $t_j$, choose a marking $D_j \subseteq \mathbb{D}$ with probability $p_{D_j}$.
3. Independently draw $Y^j = (Y^j_1,\dots,Y^j_N) \sim Q_{D_j}$ and, for every $i \in D_j$, place an event of $X_i$ at time $t_j + Y^j_i$.

Let $\bar p_D = \sum_{D' \supseteq D} p_{D'}$ be the probability that an event is copied to every neuron in $D$ (and possibly others).

**Proposition (marginals).** Each $X_i$ is a homogeneous Poisson process of rate $\lambda \bar p_{\{i\}}$. Its events are the mother events with $i$ in the marking, shifted i.i.d. according to the mixture

$$Q_i = \frac{\sum_{D\ni i} p_D\, Q_D^{\{i\}}}{\sum_{D\ni i} p_D},$$

where $Q_D^{\{i\}}$ is the $i$-th marginal of $Q_D$.

**Special cases.** With all $Q_D$ equal to the point mass at $0$:
- the *single interaction process* $X_i = Z_i + Z_c$ ($Z_i, Z_c$ independent Poisson with rates $\lambda_i, \lambda_c$) is GTaS with $\lambda = \lambda_c + \sum_i \lambda_i$, $p_{\{i\}} = \lambda_i/\lambda$, $p_{\mathbb{D}} = \lambda_c/\lambda$ and $p_D = 0$ otherwise;
- the *multiple interaction process*, obtained by independently retaining each mother event in each daughter with probability $\epsilon$, is GTaS with $p_D = \epsilon^{|D|}(1-\epsilon)^{N-|D|}$.

## Expansion

Thinning a Poisson process independently with probability $\bar p_{\{i\}}$ gives a Poisson process of rate $\lambda \bar p_{\{i\}}$, and displacing each point of a Poisson process by i.i.d. shifts leaves it a Poisson process of the same rate (displacement theorem). The joint law is described by decomposing the marked mother process into independent Poisson processes $\xi(D)$, one per subset, which gives the representation used to compute cross-cumulants of every order. The two special cases follow by matching the probability that a mother event lands in exactly the neurons of $D$.

## Sources

- J. Trousdale, Y. Hu, E. Shea-Brown, K. Josić, "A generative spike train model with time-structured higher order correlations", Frontiers in Computational Neuroscience 7 (2013) 84, Sections 2.1, 2.2.1 and 2.3 (Equations 8–10), <https://doi.org/10.3389/fncom.2013.00084>, PMCID PMC3727174.
- N. Bäuerle, R. Grübel, "Multivariate counting processes: copulas and beyond", ASTIN Bulletin 35 (2005) 379–408, <https://doi.org/10.2143/AST.35.2.2003459>.
