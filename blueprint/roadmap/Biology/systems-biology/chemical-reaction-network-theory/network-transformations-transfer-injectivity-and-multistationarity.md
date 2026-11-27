# Network transformations transfer injectivity and multistationarity

Let $(\mathscr{N},K)$ and $(\mathscr{N}^\#,K^\#)$ be kinetic systems on the same species set, with a common domain $\Omega \supseteq \mathbb{R}^m_{>0}$, stoichiometric matrices $N, N^\#$ and stoichiometric subspaces $S, S^\#$. They are *dynamically equivalent* if $N K(x) = N^\# K^\#(x)$ for all $x \in \Omega$. A dynamic equivalence is

- *S-including* if $S^\# \subseteq S$,
- *S-extending* if $S \subseteq S^\#$,
- *S-invariant* if $S^\# = S$,

and in each case $(\mathscr{N}^\#,K^\#)$ is called a *transform* of $(\mathscr{N},K)$. Shifting, dividing and merging reactions (network translation) are S-invariant; scaling, splitting and merging via reaction vectors and adding dummy reaction pairs give the other classes.

A kinetic system is *injective* if for any two distinct stoichiometrically compatible $x^*, x^{**} \in \mathbb{R}^m_{\ge 0}$, at least one positive, $NK(x^*) \ne NK(x^{**})$; it is *multistationary* if some positive stoichiometric compatibility class contains two distinct positive equilibria, and *monostationary* otherwise.

**Proposition.** Let $(\mathscr{N}^\#,K^\#)$ be a transform of $(\mathscr{N},K)$.

1. If the transformation is S-including, then injectivity of $(\mathscr{N},K)$ implies injectivity of $(\mathscr{N}^\#,K^\#)$, and monostationarity of $(\mathscr{N},K)$ implies monostationarity of $(\mathscr{N}^\#,K^\#)$.
2. If the transformation is S-extending, then non-injectivity of $(\mathscr{N},K)$ implies non-injectivity of $(\mathscr{N}^\#,K^\#)$, and multistationarity of $(\mathscr{N},K)$ implies multistationarity of $(\mathscr{N}^\#,K^\#)$.
3. If the transformation is S-invariant, all four implications hold, so injectivity and multistationarity are invariants of S-invariant transformations.

Moreover, a transformation consisting only of reactant-support-preserving shifts and divisions and of scalings preserves concordance of the underlying network; for weakly monotonic kinetics (mass action included) a concordant network is injective (Shinar-Feinberg).

## Expansion

For (1): if the transform were not injective there would be distinct $x, x'$ with $x' - x \in S^\# \subseteq S$ and $N^\# K^\#(x) = N^\# K^\#(x')$; since $N^\# K^\# = NK$ this contradicts injectivity of the original. Equilibria are common to both systems because the vector fields coincide, so two compatible positive equilibria of the transform are also compatible for the original. Part (2) is the contrapositive argument with the roles of $S$ and $S^\#$ exchanged, and (3) combines both. In applications one transforms a model into a network where a structural test (deficiency theory, concordance) is available and transfers the conclusion back.

## Sources

- Dylan Antonio Talabis, Eduardo Mendoza, "Network transformation-based analysis of biochemical systems", *Journal of Mathematical Biology* 89(6) (2024), 62, Definition 15, Proposition 15, Proposition 16 and Proposition 12, <https://doi.org/10.1007/s00285-024-02152-2> (preprint arXiv:2308.12586).
