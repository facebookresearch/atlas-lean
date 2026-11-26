# Spread families contain many pairwise disjoint members

There is an absolute constant $C$ such that every nonempty $\ell$-bounded $\kappa$-spread family $\mathcal{F}$ of nonempty sets with $\kappa \ge C\, r \log(\ell r)$ contains $r$ pairwise disjoint members (which are then distinct).

## Proof sketch

Since the members are nonempty, summing the spread condition over singletons gives $|\mathcal{F}| \le \sum_{x} |\{F : x \in F\}| \le |X|\,\kappa^{-1}|\mathcal{F}|$, so $|X| \ge \kappa \ge 2r$ for $C$ large. Split $X$ by a uniformly random partition into $r$ classes of sizes $\lfloor |X|/r \rfloor$ or $\lceil |X|/r \rceil$; each class is a uniformly random set of size at least $|X|/(2r)$. Containing a member of $\mathcal{F}$ is monotone, so by the spread lemma (applied to the nonempty family $\mathcal{F}$ with density $1/(2r)$ and $\varepsilon < 1/r$) each class contains a member with probability greater than $1 - 1/r$. A union bound over the $r$ classes gives, with positive probability, a member inside each class; members in different classes are disjoint, and being nonempty they are distinct.

## Depends on

- [Spread families and spread measures](kappa-spread-families-and-measures.md)

## Proof depends on

- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774.
- Tolson Bell, Suchakree Chueluecha, Lutz Warnke, "Note on sunflowers", Discrete Mathematics 344(7) (2021); arXiv:2009.09327, Lemma 2 and Theorem 3 (uniform versions for families of $k$-sets of size at least $r^k$).
