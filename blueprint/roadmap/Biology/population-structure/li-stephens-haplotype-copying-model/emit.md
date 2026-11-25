# Li–Stephens emission probability

Let $R$ be a field and $\varepsilon \in R$. For a copied haplotype $k$ and a [site observation](obs.md) $(h, a)$, the emission weight is

$$e_\varepsilon(k, (h, a)) = \begin{cases} 1 - \varepsilon & h_k = a,\\ \varepsilon & h_k \ne a: \end{cases}$$

for $R = \mathbb{R}$, $0 \le \varepsilon \le 1$ and a biallelic alphabet of alleles, the target allele matches the copied reference allele with probability $1 - \varepsilon$, and the weights are the conditional probabilities of the two alleles given the copied haplotype and the panel.
