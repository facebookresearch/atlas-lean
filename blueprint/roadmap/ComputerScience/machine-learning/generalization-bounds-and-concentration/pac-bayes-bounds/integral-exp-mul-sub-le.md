# Hoeffding's lemma in centred exponential form

Let $D$ be a probability measure on a measurable space $\mathcal Z$ and $g : \mathcal Z \to [0, C]$
measurable. Then for every real $t$,

$$\int \exp\Big(t \Big(\int g \, dD - g(z)\Big)\Big) \, dD(z) \le \exp(C^2 t^2 / 8).$$

This is Hoeffding's lemma (the centred variable $\int g \, dD - g$ is sub-Gaussian with variance
proxy $C^2/4$), in the form the PAC-Bayes argument uses.
