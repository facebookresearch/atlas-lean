# Kummer–Dedekind theorem

Let $R$ be an integrally closed domain and $S$ a Dedekind domain that is an $R$-algebra, torsion-free as an
$R$-module. Let $x \in S$ be integral over $R$, with minimal polynomial $f \in R[X]$, let
$\mathfrak{f} = \{a \in S : a S \subseteq R[x]\}$ be the conductor of $R[x]$ in $S$, and let $I$ be a nonzero
maximal ideal of $R$ such that $I$ and the preimage of $\mathfrak{f}$ in $R$ generate $R$. Let $\bar{f} \in (R/I)[X]$
be the reduction of $f$ modulo $I$.

The ring isomorphism $S/IS \cong (R/I)[X]/(\bar{f})$ that maps the class of $Q(x)$ to the class of $Q \bmod I$
for every $Q \in R[X]$ induces a bijection $\phi$ from the set of prime ideals of $S$ that occur in the
factorisation of $IS$ onto the set of monic irreducible factors of $\bar{f}$: the prime ideal $J$ corresponds to the
ideal $J/IS$ of $S/IS$, hence to an ideal of $(R/I)[X]$ containing $\bar{f}$, and $\phi(J)$ is its monic generator.
Then the factorisation of $IS$ corresponds to that of $\bar{f}$: the multiset of prime ideal factors of $IS$,
counted with multiplicity, is the image under $\phi^{-1}$ of the multiset of monic irreducible factors of $\bar{f}$,
counted with multiplicity.

## Sources

- F. Keune, *Number Fields*, Radboud University Press, Nijmegen (2023, version 2023-01), open access,
  <https://doi.org/10.54195/IPVU4488>, §3.1, Theorem 3.6 (Kummer–Dedekind, p. 51), for a number field $K$, a
  primitive element $\theta \in \mathcal{O}_K$ and a prime $p$ not dividing $(\mathcal{O}_K : \mathbb{Z}[\theta])$.
