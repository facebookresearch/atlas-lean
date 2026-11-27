# Spread families contain many pairwise disjoint members

There is an absolute constant $C$ such that for all integers $k \ge 1$ and $r \ge 2$ and every $\kappa \ge C\, r \log(kr)$, every family (sequence, repetitions allowed) $\mathcal{F}$ of at least $\kappa^{k}$ sets of size $k$ that is $\kappa$-spread in the absolute sense (every nonempty $Z$ lies in at most $\kappa^{k-|Z|}$ members) contains $r$ pairwise disjoint members (which are then distinct).

## Proof sketch

Summing the spread condition over singletons gives $k|\mathcal{F}| \le |X|\,\kappa^{k-1}$, so $|X| \ge k\kappa \ge r$. Split $X$ by a uniformly random partition into $r$ classes of sizes $\lfloor |X|/r \rfloor$ or $\lceil |X|/r \rceil$; each class is a uniformly random set of size at least $|X|/(2r)$. By the uniform form of the spread lemma (Rao, Lemma 4), applied with $\gamma = 1/(2r)$ and $\varepsilon = 1/(r+1)$, which needs $\kappa \ge 2\beta r\log(k(r+1))$, true for $C$ large, each class contains a member with probability greater than $1 - 1/(r+1)$. A union bound over the $r$ classes gives, with positive probability, a member inside each class; members in different classes are disjoint, and being nonempty they are distinct (Rao, Lemma 2).

## Depends on

- [Spread families and spread measures](kappa-spread-families-and-measures.md)

## Proof depends on

- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774 (Lemma 2 and its proof from Lemma 4).
- Tolson Bell, Suchakree Chueluecha, Lutz Warnke, "Note on sunflowers", Discrete Mathematics 344(7) (2021); arXiv:2009.09327, Lemma 2 and Theorem 3 (uniform versions for families of $k$-sets of size at least $r^k$).
