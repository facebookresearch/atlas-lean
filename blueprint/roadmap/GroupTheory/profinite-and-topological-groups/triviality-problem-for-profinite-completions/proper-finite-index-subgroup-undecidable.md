# Having a proper finite-index subgroup is undecidable for finitely presented groups

There is no algorithm that decides whether a finitely presented group has a proper subgroup of finite index, equivalently a non-trivial finite quotient, equivalently a non-trivial profinite completion.

There is no algorithm that, given a finite presentation of a group $G$, determines whether $G$ has a proper subgroup of finite index (Theorem A of the source). Precisely, there is a recursive sequence of finite presentations of groups $G_n$ such that

$$
\{ n \in \mathbb{N} : G_n \text{ has a proper subgroup of finite index} \}
$$

is recursively enumerable but not recursive. Since a group has a proper finite-index subgroup exactly when it has a non-trivial finite quotient, exactly when its profinite completion $\widehat{G}$ is non-trivial, the triviality problem for profinite completions of finitely presented groups is undecidable; equivalently, the existence of a non-trivial finite-dimensional linear representation (over any field) is undecidable.

The property stays undecidable in restricted classes: there is no algorithm that determines whether a compact non-positively curved square complex has a non-trivial connected finite-sheeted covering (Theorem B), nor whether a biautomatic group has a proper subgroup of finite index (Corollary 7.9). The property $\widehat{G} \cong 1$ is neither a Markov nor a co-Markov property, so the Adian–Rabin method does not apply.

## Depends on

- [Profinite completion](../profinite-rigidity/profinite-completion.md)
- [Group](../../group-basics/group.md)

## Proof depends on

- [A finitely presented group in which triviality in all finite quotients is undecidable](triviality-in-finite-quotients-undecidable.md)

## Expansion

The Encoding Theorem (Theorem C of the source) gives an algorithm that takes a finite presentation $\langle A \mid R \rangle$ of a group $G$ and a word $w \in F(A)$ and outputs a finite presentation of a group $G_w$ with $\widehat{G_w} \cong 1$ if and only if $w = 1$ in $\widehat{G}$. Applied to Slobodskoi's group, with $w$ running through the words, it turns the undecidable set of words trivial in $\widehat{G}$ into an undecidable set of presentations with trivial profinite completion. The proof of the Encoding Theorem rests on a strengthening of Wise's omnipotence for virtually free groups and on constructions of malnormal subgroups.

## Sources

- M. R. Bridson and H. Wilton, "The triviality problem for profinite completions", Inventiones Mathematicae 202 (2015), no. 2, 839–874, https://doi.org/10.1007/s00222-015-0578-8; arXiv:1401.2273v3 (Theorems A, B and C, Corollary 7.9, of arXiv:1401.2273v3).
