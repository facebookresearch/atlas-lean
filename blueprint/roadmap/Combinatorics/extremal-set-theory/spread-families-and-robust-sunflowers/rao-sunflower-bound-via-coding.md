# Rao: sunflower bound via the converse of Shannon's source coding theorem

There is an absolute constant $C$ such that every family of more than $\big(C\, r \log(\ell r)\big)^{\ell}$ sets of size $\ell$ contains an $r$-sunflower. (This simplifies and slightly sharpens the Alweiss-Lovett-Wu-Zhang bound $(\log \ell)^{\ell}(r\log\log \ell)^{O(\ell)}$.)

## Proof sketch

Let $\kappa = C r\log(\ell r)$ and let $\mathcal{F}$ be a family of more than $\kappa^{\ell}$ distinct sets of size $\ell$; we may assume $r \ge 2$. Take $S$ of maximum size with $|\mathcal{F}_S| > \kappa^{\ell-|S|}$, where $\mathcal{F}_S = \{F \setminus S : F \in \mathcal{F}, F \supseteq S\}$ ($S = \emptyset$ qualifies). Then $|S| < \ell$, since $|\mathcal{F}_S| \le 1$ when $|S| = \ell$, and by maximality every nonempty $Z$ disjoint from $S$ lies in at most $\kappa^{\ell-|S|-|Z|}$ members of $\mathcal{F}_S$: the link is a family of $k = \ell - |S|$ element sets, $\kappa$-spread in the absolute sense, with more than $\kappa^{k}$ members. If $k = 1$, the link has more than $\kappa \ge r$ singletons $\{x_i\}$, and $r$ of the sets $S \cup \{x_i\}$ form an $r$-sunflower. If $k \ge 2$, the binomial form of the spread lemma with $\delta = \varepsilon = 1/r$ (which needs $\kappa \ge B r \log(kr)$, true for $C \ge B$) shows that a random set of density $1/r$ contains a member of the link with probability greater than $1 - 1/r$. The subfamily $\{F \in \mathcal{F} : F \supseteq S\}$ has at least two members, so its kernel $K \supseteq S$ is not one of them, and $F \setminus K \subseteq F \setminus S$; hence it is a $(1/r, 1/r)$-robust sunflower and contains an $r$-sunflower of $\mathcal{F}$.

## Depends on

- [Sunflower](../intersecting-families/sunflower-lemma/is-sunflower.md)

## Proof depends on

- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)
- [Robust sunflowers contain sunflowers](robust-sunflowers-contain-sunflowers.md)
- [Alweiss–Lovett–Wu–Zhang sunflower bound](../intersecting-families/sunflower-lemma/theorem-1-4.md)

## Sources

- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774 (Lemmas 2 and 4 and the reduction to spread sequences in Section 1).
