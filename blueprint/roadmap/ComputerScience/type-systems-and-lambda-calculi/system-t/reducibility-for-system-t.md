# Reducibility for System T

For [Gödel's System T](godel-s-system-t.md) define, by induction on types, the set $\mathrm{RED}_A$ of *reducible* terms of type $A$: a term of type $\mathrm{nat}$ is reducible if
it is strongly normalizing, and $t : A \to B$ is reducible if $t\, u \in \mathrm{RED}_B$ for every $u \in \mathrm{RED}_A$. Call a term *neutral* if it is not an abstraction, $0$ or
$\mathrm{S}\, t$. Then, for every type $A$:

- (CR1) every $t \in \mathrm{RED}_A$ is strongly normalizing;
- (CR2) if $t \in \mathrm{RED}_A$ and $t \to t'$, then $t' \in \mathrm{RED}_A$;
- (CR3) if $t$ is neutral and every one-step reduct of $t$ is in $\mathrm{RED}_A$, then $t \in \mathrm{RED}_A$; in particular neutral normal terms, such as variables, are reducible.

Moreover $0$ is reducible; $\mathrm{S}\, t$ is reducible when $t$ is; $\lambda x.\, v$ is reducible when $v[u/x]$ is reducible for every reducible $u$; and the *recursor
lemma* holds: if $u$, $v$ and $t$ are reducible, then $\mathrm{R}_A\, u\, v\, t$ is reducible. The recursor lemma is proved by induction on
$\nu(u) + \nu(v) + \nu(t) + \ell(t)$, where $\nu$ is the maximal length of a reduction sequence and $\ell(t)$ the number of symbols in the normal form of $t$: the
reduct $v\, w\, (\mathrm{R}_A\, u\, v\, w)$ of $\mathrm{R}_A\, u\, v\, (\mathrm{S}\, w)$ is handled by $\nu(w) = \nu(t)$ and $\ell(w) < \ell(t)$, so the induction hypothesis makes
$\mathrm{R}_A\, u\, v\, w$ reducible, and then $v\, w\, (\mathrm{R}_A\, u\, v\, w)$ is reducible by the definition at arrow types. By induction on terms, every term with reducible terms substituted for its free variables is reducible.

## Depends on

- [Gödel's System T](godel-s-system-t.md)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, <https://courses.grainger.illinois.edu/cs522/sp2016/ProofAndTypes.pdf>: Chapter 6, Sections 6.1–6.3 (reducibility, neutrality, (CR 1)–(CR 3), the pairing and abstraction lemmas and the reducibility theorem for the simply typed calculus), and Chapter 7, Section 7.2 (the extension to T, with items 1–4 of the proof, item 4 being the recursor case).
- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 11.6.4 (strong normalization of T by Tait's method).
