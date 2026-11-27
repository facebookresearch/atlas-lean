# p-adic monodromy theorem

Let $K$ be a finite extension of $\mathbb{Q}_p$. A $p$-adic representation of $G_K$ is de Rham if and only if it
is potentially semistable: for every de Rham representation $V$ there is a finite extension $K'/K$ in $\bar K$
such that $V|_{G_{K'}}$ is semistable. (The converse, that potentially semistable representations are de Rham,
is elementary.)

## Depends on

- [de Rham representations](de-rham-representations.md)
- [Semistable and potentially semistable representations](semistable-representations.md)

## Proof depends on

- [(φ, Γ)-modules and p-adic differential equations](phi-gamma-modules-and-p-adic-differential-equations.md), for Berger's construction of a $p$-adic differential equation with Frobenius structure from a de Rham representation and Crew's conjecture on its quasi-unipotence (proved by André, Kedlaya and Mebkhout)

## Sources

- L. Berger, "Représentations p-adiques et équations différentielles", Invent. Math. 148 (2002), 219–284,
  author's version <https://perso.ens-lyon.fr/laurent.berger/articles/article02.pdf>: Théorème 0.7 ("Si $V$ est
  une représentation de de Rham, alors $V$ est potentiellement semi-stable"), deduced in the introduction from
  the quasi-unipotence of $N_{\mathrm{dR}}(V)$ proved by André, Kedlaya and Mebkhout; it is Corollaire 5.22 of the
  paper.
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §8.3.1, Theorem A and Remark 8.50 (the $p$-adic monodromy conjecture, first proved by Berger).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the theorem as `GlobalTheory.Published.DeRhamPotSemistable`.
