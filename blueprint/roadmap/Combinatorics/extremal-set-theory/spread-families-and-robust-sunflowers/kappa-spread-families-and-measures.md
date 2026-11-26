# Spread families and spread measures

Let $X$ be a finite set and $\mathcal{F}$ a family (multiset) of subsets of $X$. For $\kappa > 1$, $\mathcal{F}$ is *$\kappa$-spread* if for every $S \subseteq X$,

$$
\big|\{F \in \mathcal{F} : S \subseteq F\}\big| \le \kappa^{-|S|}\, |\mathcal{F}| .
$$

More generally a probability measure $\nu$ on $2^X$ is $\kappa$-spread if $\nu(\{F : F \supseteq S\}) \le \kappa^{-|S|}$ for all $S$. A family is *$\ell$-bounded* if all members have size at most $\ell$. The counting condition is vacuous for the empty family, which is $\kappa$-spread for every $\kappa$, and the family $\{\emptyset\}$ is $\kappa$-spread as well; results that produce members of a spread family therefore assume $\mathcal{F}$ nonempty, and results that produce disjoint members assume in addition that its members are nonempty.

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
- Keith Frankston, Jeff Kahn, Bhargav Narayanan, Jinyoung Park, "Thresholds versus fractional expectation-thresholds", Annals of Mathematics 194(2) (2021); arXiv:1910.13433.
