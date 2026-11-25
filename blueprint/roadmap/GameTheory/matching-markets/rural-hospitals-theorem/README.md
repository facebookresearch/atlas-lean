# Rural hospitals theorem

In the medical residency market, some hospitals, often rural ones, fill fewer positions than they offer. Roth (1986) shows that this is a property of every stable outcome: every stable outcome fills the same number of positions at each hospital and assigns the same set of students (his Lemma 1, from Roth 1984 and Gale–Sotomayor 1985), and a hospital that is short of its quota at one stable outcome receives exactly the same students at every stable outcome (his Theorem). So no change of clearinghouse procedure that keeps the outcome stable can change the staffing of the hospitals that are left short.

This topic treats the marriage case, where every quota equals one: in a finite market where agents may remain single, every stable matching matches the same men and the same women. The women play Roth's hospitals and the men his students; for a woman the statement is the Theorem with quota one: single at one stable matching, single at all. Roth's college-admissions setting has quotas larger than one and responsive preferences.

A matching with singles is a partial bijection $\mu$ between the men $M$ and the women $W$: $\mu(m)$ is the partner of man $m$ and $\mu^{-1}(w)$ that of woman $w$, if any; an agent without a partner is single. A perfect matching $\mu : M \to W$ of the [stable marriage problem](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/README.md) is the partial bijection in which everybody has a partner; when every partner is preferred to remaining single, the two notions of stability agree, and every stable matching with singles is then perfect, so the theorem says nothing new in that model.

## The model with singles

- [Men's preferences with the option of remaining single](mprefs-single.md)
- [Women's preferences with the option of remaining single](wprefs-single.md)
- [Stable matching with singles](is-stable-single.md)
- [Stability does not depend on which side is called the men](stability-with-singles-symmetric.md)

## The theorem

- [A man matched at one stable matching is matched at every stable matching](matched-man-matched-at-every-stable-matching.md)
- [Rural hospitals theorem, marriage case: every stable matching matches the same men](rural-hospitals-same-men.md)
- [Rural hospitals theorem, marriage case: every stable matching matches the same women](rural-hospitals-same-women.md)

## Complete preference lists

- [Remaining single ranked last](single-ranked-last.md)
- [Bridge to the stable marriage model](stable-with-singles-iff-stable-perfect-matching.md)
- [With complete lists every stable matching is perfect](complete-lists-stable-matchings-are-perfect.md)

## Related topics

- [Stable marriage problem](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/README.md): the model without singles, with perfect matchings between sides of equal size.
- [Lattice of stable matchings](../lattice-of-stable-matchings/README.md): the men's join of stable matchings, which Roth's proof of the Theorem uses in the college-admissions case (his Lemma 2).
