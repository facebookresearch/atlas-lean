# PAC and PRC fields are finitely undecidable

Every pseudo-algebraically closed field and every pseudo-real closed field is finitely undecidable in the language of rings: no finitely axiomatized part of its theory is decidable. In particular no such field is finitely axiomatizable.

**Setting.** A field $K$ is *pseudo-algebraically closed* (PAC) if every geometrically irreducible $K$-variety has a $K$-rational point, and *pseudo-real closed* (PRC) if every geometrically irreducible variety over $K$ that has a smooth point in each real closure of $K$ has a $K$-rational point. Theories are taken in the language of rings.

**Theorem (Tyrrell).**

1. Every PAC field is [finitely undecidable](finitely-undecidable-theories.md) (Corollary 3.19).
2. Every PRC field is finitely undecidable (Corollary 4.16).

Moreover no PAC field is finitely axiomatizable, even among the PAC fields of the same characteristic and degree of imperfection (Theorem 3.21), and no PRC field is finitely axiomatizable (Corollary 4.17). A PRC field that is not formally real is PAC, so clause 2 extends clause 1.

## Depends on

- [Finitely undecidable theories](finitely-undecidable-theories.md)
- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The theory of graphs is hereditarily undecidable](../theories-of-finite-structures/theory-of-graphs-is-hereditarily-undecidable.md)

## Expansion

For a finite subtheory $\Sigma$ of the theory of a PAC field $K$ and any nonempty graph $\Gamma$, the methods of Cherlin, van den Dries and Macintyre and of Ershov give a PAC field $K_\Gamma \models \Sigma$ in which $\Gamma$ is interpretable, uniformly in $\Gamma$ (Theorem 3.18). Since the theory of graphs is hereditarily undecidable, uniform interpretability of all nonempty graphs in models of $\Sigma$ makes $\Sigma$ undecidable. For formally real PRC fields the construction adapts work of Haran and Jarden (Theorem 4.15). For pseudo-$p$-adically closed fields the method yields only that no bounded such field is finitely axiomatizable (Theorem 5.10).

## Sources

- B. Tyrrell, "Finite undecidability in PAC and PRC fields", *Annals of Pure and Applied Logic* 175(10):103465, 2024, doi:10.1016/j.apal.2024.103465; read as arXiv:2212.12918v2, <https://arxiv.org/abs/2212.12918v2>, titled there "Finite Undecidability in Fields II: PAC, PRC and PpC Fields": Corollaries 3.19, 4.16 and 4.17, Theorems 3.18, 3.21, 4.15 and 5.10, and Sections 3–5 of arXiv:2212.12918v2.
