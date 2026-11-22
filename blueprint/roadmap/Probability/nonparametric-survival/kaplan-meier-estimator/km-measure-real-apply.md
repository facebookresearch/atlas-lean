# Mass of a set under the Kaplan–Meier measure

For [grouped right-censored data](censored-data.md), $\tau \in \mathbb{R}$ and a measurable set $B \subseteq \mathbb{R}$, the [Kaplan–Meier measure](km-measure.md) gives $B$ the mass

$$\sum_{j : t_j \in B} \hat S(t_j^-)\, \frac{d_j}{n_j} + \mathbf{1}_B(\tau) \prod_{j=1}^{k} \Big(1 - \frac{d_j}{n_j}\Big).$$
