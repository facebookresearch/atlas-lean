# Bell-Chueluecha-Warnke: sunflower bound O(r log l)^l

There is an absolute constant $C$ such that, for all integers $r, \ell \ge 2$, every family of at least $(C r \log \ell)^{\ell}$ distinct sets of size $\ell$ contains an $r$-sunflower.

## Proof sketch

Induct on $\ell$ with $\kappa = C r \log \ell$. If the family is $\kappa$-spread, partition the ground set uniformly at random into $2r$ classes; each class is distributed as a random set of density $1/(2r)$, so the spread lemma with failure probability $1/4$ shows that each class contains a member with probability at least $3/4$. By linearity of expectation some partition has at least $3r/2 \ge r$ classes containing a member, and $r$ such members are pairwise disjoint, an $r$-sunflower with empty kernel. Otherwise some non-empty set $T$ lies in more than $\kappa^{\ell - |T|}$ members, and induction applied to the link of $T$ (or, when $|T| = \ell - 1$, picking $r$ of its more than $\kappa \ge r$ singletons) gives an $r$-sunflower whose petals all contain $T$. The union bound over only $r$ classes used by Rao needs failure probability $1/r$, which costs the extra $\log r$.

## Depends on

- [Sunflower](../intersecting-families/sunflower-lemma/is-sunflower.md)

## Proof depends on

- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)
- [Sunflower-free families have spread links](sunflower-free-families-have-spread-restrictions.md)

## Sources

- Tolson Bell, Suchakree Chueluecha, Lutz Warnke, "Note on sunflowers", Discrete Mathematics 344(7) (2021); arXiv:2009.09327.
