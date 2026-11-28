# Contractibility of the full lifted Salvetti realization

Let $M$ be a Coxeter matrix on any finite set $S$ (including empty and disconnected diagrams), with Artin group $A$ and Coxeter group $W$. Call $T\subseteq S$ spherical if the corresponding subgroup $W_T$ of $W$ is finite. Lifted cells are pairs $(a,T)$ with $a\in A$ and $T$ spherical. A face relation from $(a,T)$ to $(b,U)$ requires $T\subseteq U$ and a word in $U$ whose Coxeter element is reduced and satisfies $\ell_W(w)\le\ell_W(wv)$ for every $v\in W_T$, where $w$ is the Coxeter element represented by the word, and whose Artin lift $\widetilde w$ satisfies $a=b\widetilde w$. Take reflexive transitive closure of this relation and geometrically realize its preorder nerve. This whole realization is contractible. The inclusion of all spherical subsets is essential, and the Artin and Coxeter groups need not be finite.

## Depends on

- [Artin group presentation](artin-group.md)
- Existing Artin presentation, finite Coxeter parabolics, lifted-face preorder and geometric realization of its nerve.

## Proof depends on

- Identify the lifted model with the universal Salvetti cover and prove contraction for arbitrary finite-rank diagrams.

## Expansion

Prove the reduced-coset representative incidence description rather than replacing the lifted order by a poset on spherical subsets alone. Then isolate the harmonic height and contraction steps.

## Sources

- OpenAI Math, [`salvetti_cover_contractible`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HarmonicArtin.lean#L57-L62) (statement and local definitions).
- OpenAI Math, [lifted-face relation and preorder](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HarmonicArtin.lean#L40-L55).
