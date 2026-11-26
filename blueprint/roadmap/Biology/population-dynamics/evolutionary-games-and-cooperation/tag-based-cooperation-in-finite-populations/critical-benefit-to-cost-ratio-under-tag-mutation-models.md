# Critical benefit-to-cost ratio under three tag-mutation models

Under the hypotheses of the [risk-dominance condition for tag-based cooperation](risk-dominance-condition-for-tag-based-cooperation.md) (weak selection, rare symmetric mutation, large $N$), tag-based cooperators are more abundant than defectors iff $b/c > 1 + 2u/v$, where $u$ is the rate of mutations changing only the strategy and $v$ the rate of mutations changing strategy and tag together. Three choices of $u$ and $v$ give the following thresholds (Traulsen and Nowak 2007, eqs. (9)–(11)).

1. **Separate strategy and tag bits.** The genotype is a bit string with one strategy bit and $L$ tag bits, each mutating independently with probability $\mu$ per replication. Neglecting multiple tag mutations, $u = \mu(1 - \mu)^L$ and $v = \mu^2 L (1 - \mu)^{L - 1}$, so the condition is

$$\frac{b}{c} > 1 + \frac{2(1 - \mu)}{\mu L}.$$

For the small $\mu$ that the rare-mutation analysis requires, the threshold is very large.

2. **One pleiotropic gene.** The parity of the first $n$ bits of a gene sets the strategy and its last $m$ bits set the tag, with an overlap of $L$ bits ($1 \le L \le n$). To first order in $\mu$, $u = (n - L)\mu$ and $v = L\mu$, so

$$\frac{b}{c} > 1 + \frac{2(n - L)}{L} = \frac{2n - L}{L},$$

which is small as soon as the overlap $L$ is a sizable fraction of $n$.

3. **Cultural model with uniform phenotype mutation.** All $2K$ (tag, strategy) phenotypes mutate into each other at the same rate $\mu$. Then $u = \mu$ and $v = (K - 1)\mu$, and the condition is

$$\frac{b}{c} > \frac{K + 1}{K - 1}.$$

With $K = 2$ tags this is $b/c > 3$; as $K \to \infty$ the threshold decreases to $1$, so with many tags cooperation needs only $b > c$.

## Depends on

- [Risk-dominance condition for tag-based cooperation](risk-dominance-condition-for-tag-based-cooperation.md)

## Proof sketch

Each case is a substitution into $1 + 2u/v$. In case 1, $u/v = (1 - \mu)/(\mu L)$. In case 2, $u/v = (n - L)/L$. In case 3, $u/v = 1/(K - 1)$ and $1 + 2/(K - 1) = (K + 1)/(K - 1)$. Read together, the cases separate genetic architectures: when tag and behaviour are encoded by independent loci, a simultaneous change requires two mutations and $v$ is of order $\mu^2$, so the threshold blows up and well-mixed tag-based cooperation is not expected; when one gene encodes both, or when imitation changes the whole phenotype at once, $v$ is comparable to or larger than $u$ and moderate benefit-to-cost ratios suffice.

## Sources

- A. Traulsen and M. A. Nowak, "Chromodynamics of cooperation in finite populations", PLoS ONE 2 (2007), e270, Results and Discussion, eqs. (8)–(11), <https://doi.org/10.1371/journal.pone.0000270>, PMCID PMC1803018.
