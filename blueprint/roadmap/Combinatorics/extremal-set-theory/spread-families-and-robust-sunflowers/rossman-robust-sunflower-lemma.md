# Rossman's robust sunflower lemma and monotone clique lower bounds

Every $\ell$-uniform family of more than $\ell!\,(C\log(1/\beta)/\alpha)^{\ell}$ sets, for an absolute constant $C$, contains an $(\alpha, \beta)$-robust sunflower (Rossman), and Alweiss-Lovett-Wu-Zhang improve the threshold to $(C\log(\ell/\beta)/\alpha)^{\ell}$. Robust sunflowers replace sunflowers in Razborov's approximation method, yielding average-case monotone circuit lower bounds such as $\omega(n^{k/4})$ for detecting $k$-cliques in random graphs at the threshold density.

## Proof sketch

Rossman's bound follows from Janson's inequality applied inside links of maximal size, in the style of the Erdős-Rado induction. The spread-lemma bound follows by passing to a spread link and applying the spread lemma with density $\alpha$ and failure probability $\beta$.

## Depends on

- [Robust sunflowers](robust-sunflowers-and-satisfying-systems.md)
- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)
- [Sunflower-free families have spread links](sunflower-free-families-have-spread-restrictions.md)

## Proof depends on

- [Robust sunflowers](robust-sunflowers-and-satisfying-systems.md)
- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)
- [Sunflower-free families have spread links](sunflower-free-families-have-spread-restrictions.md)

## Sources

- Benjamin Rossman, "The monotone complexity of k-clique on random graphs", SIAM Journal on Computing 43(1) (2014), FOCS (2010).
- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
