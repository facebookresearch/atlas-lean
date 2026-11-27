# Rao: sunflower bound via the converse of Shannon's source coding theorem

There is an absolute constant $C$ such that every family of more than $\big(C\, r \log(\ell r)\big)^{\ell}$ sets of size $\ell$ contains an $r$-sunflower. (This simplifies and slightly sharpens the Alweiss-Lovett-Wu-Zhang bound $(\log \ell)^{\ell}(r\log\log \ell)^{O(\ell)}$.)

## Proof sketch

Pass to a $\kappa$-spread link with $\kappa = C r\log(\ell r)$. By the spread lemma with $\varepsilon = 1/r$ a random set of density $1/r$ contains a member of the link with probability at least $1 - 1/r$, so the link is a $(1/r, 1/r)$-robust sunflower and contains an $r$-sunflower, which together with $S$ gives an $r$-sunflower in $\mathcal{F}$.

## Depends on

- [Sunflower](../intersecting-families/sunflower-lemma/is-sunflower.md)

## Proof depends on

- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)
- [Sunflower-free families have spread links](sunflower-free-families-have-spread-restrictions.md)
- [Robust sunflowers contain sunflowers](robust-sunflowers-contain-sunflowers.md)
- [Alweiss–Lovett–Wu–Zhang sunflower bound](../intersecting-families/sunflower-lemma/theorem-1-4.md)

## Sources

- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774.
