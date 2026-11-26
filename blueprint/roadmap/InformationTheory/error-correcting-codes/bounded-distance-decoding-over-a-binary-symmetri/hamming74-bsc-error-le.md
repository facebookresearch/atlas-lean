# Block-error bound for the Hamming (7,4) code over a binary symmetric channel

Let $\mathrm{enc} : \mathbb{F}_2^4 \to \mathbb{F}_2^7$ be the Hamming (7,4) encoder and $\mathrm{dec} : \mathbb{F}_2^7 \to \mathbb{F}_2^7$ its syndrome decoder. Let $0 \le \delta \le 1$ and let $\mu_\delta$ be the binary symmetric channel law on $\mathbb{F}_2^7$ (seven independent Bernoulli($\delta$) flips). Then for every message $m \in \mathbb{F}_2^4$,

$$\mu_\delta\{e : \mathrm{dec}(\mathrm{enc}(m) + e) \ne \mathrm{enc}(m)\} \le \sum_{i=2}^{7} \binom{7}{i} \delta^i (1-\delta)^{7-i}.$$
