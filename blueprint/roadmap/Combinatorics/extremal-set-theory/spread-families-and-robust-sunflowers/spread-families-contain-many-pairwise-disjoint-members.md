# Spread families contain many pairwise disjoint members

There is an absolute constant $C$ such that every $\ell$-bounded $\kappa$-spread family $\mathcal{F}$ with $\kappa \ge C\, r \log(\ell r)$ contains $r$ pairwise disjoint members.

## Proof sketch

Colour the ground set uniformly with $r$ colours. Each colour class is a random set of density $1/r \ge C\log(\ell r)/\kappa$, so by the spread lemma with $\varepsilon < 1/r$ it contains a member of $\mathcal{F}$ with probability greater than $1 - 1/r$. A union bound over the $r$ classes gives, with positive probability, one member inside each class, and members in different classes are disjoint.

## Depends on

- [Spread families and spread measures](kappa-spread-families-and-measures.md)

## Proof depends on

- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774.
