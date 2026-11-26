# Random dictatorship has metric distortion 3 - 2/n

The randomized rule that picks a voter uniformly at random and outputs her top choice has metric distortion exactly $3 - \tfrac{2}{n}$ for $n$ voters. Every randomized rule has distortion at least $2$ when the number of candidates is unbounded.

## Proof sketch

For the upper bound, $\mathbb{E}[\mathrm{SC}(\mathrm{top}(u))] = \frac{1}{n} \sum_u \sum_v d(v, \mathrm{top}(u))$ and $d(v, \mathrm{top}(u)) \le d(v, o) + d(o, u) + d(u, \mathrm{top}(u)) \le d(v, o) + 2 d(u, o)$, with the diagonal terms $u = v$ contributing only $d(v, \mathrm{top}(v)) \le d(v,o)$; summing gives $(3 - 2/n)\,\mathrm{SC}(o)$. For the lower bound, take many candidates each ranked first by one voter and a metric where the optimum is a hidden common point.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Proof depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Sources

- E. Anshelevich, J. Postl, "Randomized Social Choice Functions Under Metric Preferences", Journal of Artificial Intelligence Research 58 (2017); IJCAI 2016.
