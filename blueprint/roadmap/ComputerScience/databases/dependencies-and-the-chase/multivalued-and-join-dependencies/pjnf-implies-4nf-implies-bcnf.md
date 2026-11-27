# Project-join normal form implies fourth normal form, which implies BCNF

Let $(U, \Sigma)$ be a relation schema whose dependencies $\Sigma$ are functional, multivalued and join dependencies. If
$(U, \Sigma)$ is in [project-join normal form](project-join-normal-form.md) then it is in
[fourth normal form](fourth-normal-form.md), and if it is in fourth normal form then it is in Boyce–Codd normal form: for
every nontrivial functional dependency $X \to Y$ implied by $\Sigma$, the set $X$ is a superkey. 4NF and BCNF are both
tested on the functional and multivalued dependencies implied by $\Sigma$, join dependencies included, so a premise such as
$\bowtie[AB, BC, AC]$ is allowed.

## Depends on

- [Fourth normal form](fourth-normal-form.md)
- [Project-join normal form](project-join-normal-form.md)
- [BCNF](../../lossless-decomposition-and-normal-forms/is-bcnf.md)

## Proof depends on

- [Heath's theorem](../../lossless-decomposition-and-normal-forms/join-project-eq-of-holds-in.md)
- [Lossless binary decompositions](../../lossless-decomposition-and-normal-forms/lossless-join-iff.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Exercise 11.7(b) and (c) (p. 267) and the remark after Definition 11.2.2 (p. 252).
- R. Fagin, "Normal forms and relational database operators", *Proceedings of ACM SIGMOD*, 1979, Theorem 5 (PJ/NF implies 4NF).
