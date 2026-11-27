# Spread lemma: random sets of moderate density contain members of spread families

There is an absolute constant $C$ such that the following holds. Let $\mathcal{F}$ be a nonempty $\ell$-bounded $\kappa$-spread family on $X$, let $\varepsilon \in (0, 1/2)$, and let $W \subseteq X$ be a uniformly random subset of size $\delta |X|$ with $\delta \ge C \log(\ell/\varepsilon)/\kappa$. Then

$$
\Pr\big[\exists F \in \mathcal{F} : F \subseteq W\big] \ge 1 - \varepsilon .
$$

## Proof sketch

Rao's encoding argument: if $W$ contains no member, then for each $F$ the "minimal fragment" $F \setminus W'$ remaining after removing a random $W'$ is nonempty and can be specified by encoding $W \cup F'$ for a carefully chosen $F' \in \mathcal{F}$ plus a short description of the fragment. Spreadness makes each fragment of size $t$ cost about $t\log\kappa$ bits saved, while describing it costs $t \log(\ell)$-type bits; Shannon's source coding converse (a uniform distribution cannot be compressed) turns this into the probability bound.

## Depends on

- [Spread families and spread measures](kappa-spread-families-and-measures.md)

## Sources

- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774.
- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
- Tolson Bell, Suchakree Chueluecha, Lutz Warnke, "Note on sunflowers", Discrete Mathematics 344(7) (2021); arXiv:2009.09327.
