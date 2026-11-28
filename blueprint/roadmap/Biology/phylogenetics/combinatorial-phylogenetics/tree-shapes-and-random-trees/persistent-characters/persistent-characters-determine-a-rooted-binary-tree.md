# Persistent characters determine a rooted binary tree

**Setting.** Persistent characters on a rooted binary phylogenetic $X$-tree $T$ (with a root edge whose outer endpoint has state $0$) are as in the companion article; write $\mathfrak p(f,T)\in\{p,np\}$ for the *persistence status* of $f$ on $T$. Let $T^u$ be the unrooted tree obtained by suppressing the root, $\Sigma^*(T^u)$ its set of nontrivial splits ($|\Sigma^*(T^u)|=n-3$ for $n=|X|$), and for $\sigma=A|B$ let $f_\sigma$ and $\bar f_\sigma$ be the two binary characters with $f_\sigma^{-1}(1)=A$, respectively $B$. Let $\mathcal A^p_T=\{f_\sigma,\bar f_\sigma : \sigma\in\Sigma^*(T^u)\}$.

**Theorem.**

1. (*Buneman-type theorem*) If $\widetilde T$ is a rooted binary phylogenetic $X$-tree on which every character of $\mathcal A^p_T$ is persistent, then $\widetilde T^u=T^u$. Thus the $2(n-3)$ characters of $\mathcal A^p_T$ with status $p$ determine the unrooted tree.
2. A non-constant binary character has $l(f,T)=1$ if and only if both $f$ and $\bar f$ are persistent on $T$; if $l(f,T)=2$ and $f$ is persistent, then $\bar f$ is not.
3. Adding at most three further carefully chosen characters fixes the root position: $2(n-3)+3=2n-3$ characters together with their persistence status distinguish $T$ from every other rooted binary phylogenetic $X$-tree (two extra characters suffice when $n=4$).

## Depends on

- [Number of persistent characters via the Sackin index](number-of-persistent-characters-via-the-sackin-index.md)
- [Splits-equivalence theorem](../../../splits-compatibility-ultrametrics-and-upgma/splits-equivalence.md)

## Expansion

By part 2, both $f_\sigma$ and $\bar f_\sigma$ are persistent on $\widetilde T$ exactly when $\sigma$ has parsimony score $1$ on $\widetilde T$, that is, when $\sigma$ is a split of $\widetilde T^u$; so $\widetilde T^u$ contains all $n-3$ nontrivial splits of $T^u$ and, being binary, equals it. Rootings of a fixed unrooted tree differ only in which edge carries the root; a character that is persistent for one rooting and not for another detects the root edge, and a case analysis on the two maximal pending subtrees of the root shows that three such characters (two for $n=4$) separate all rootings.

## Sources

- K. Wicke and M. Fischer, *Combinatorial views on persistent characters in phylogenetics*, arXiv:1802.02520 (2018). <https://doi.org/10.48550/arXiv.1802.02520> Theorem 3, Lemmas 7–8, Corollary 3, Theorem 4 and Lemma 9 (Section 3). Published version: Advances in Applied Mathematics 119 (2020) 102046, <https://doi.org/10.1016/j.aam.2020.102046>.
