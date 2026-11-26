# Robust sunflowers

Let $0 < \alpha, \beta < 1$. A family $\mathcal{F}$ of subsets of $X$ with kernel $K = \bigcap_{F \in \mathcal{F}} F$ is an *$(\alpha, \beta)$-robust sunflower* (Rossman's *quasi-sunflower*) if $K \notin \mathcal{F}$ and, for $W \subseteq X$ obtained by including each element independently with probability $\alpha$,

$$
\Pr_W\big[\exists F \in \mathcal{F} : F \setminus K \subseteq W\big] > 1 - \beta .
$$

## Depends on

- [Sunflower](../intersecting-families/sunflower-lemma/is-sunflower.md)
- [Spread families and spread measures](kappa-spread-families-and-measures.md)

## Sources

- Benjamin Rossman, "The monotone complexity of k-clique on random graphs", SIAM Journal on Computing 43(1) (2014), FOCS (2010).
- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
