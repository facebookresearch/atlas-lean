# Sunflower-free families have spread links

Let $\kappa > 1$ and let $\mathcal{F}$ be an $\ell$-uniform family of distinct sets with $|\mathcal{F}| > \kappa^{\ell}$. Then there is a set $S$ with $|S| < \ell$ such that the link $\mathcal{F}_S = \{F \setminus S : F \in \mathcal{F}, F \supseteq S\}$ is $\kappa$-spread and has at least $\kappa^{\ell - |S|}$ members.

## Proof sketch

Take $S$ maximizing $|\mathcal{F}_S|\,\kappa^{|S|}$ (with $S = \emptyset$ allowed). For any $T$ disjoint from $S$, maximality gives $|\mathcal{F}_{S \cup T}| \kappa^{|S| + |T|} \le |\mathcal{F}_S|\kappa^{|S|}$, i.e. $|\{G \in \mathcal{F}_S : G \supseteq T\}| \le \kappa^{-|T|}|\mathcal{F}_S|$, which is spreadness; $|S| < \ell$ because $|\mathcal{F}| > \kappa^{\ell}$ while $|\mathcal{F}_S| \le 1$ when $|S| = \ell$ (the members of $\mathcal{F}$ are distinct) and $\mathcal{F}_S$ is empty when $|S| > \ell$.

## Depends on

- [Spread families and spread measures](kappa-spread-families-and-measures.md)

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
