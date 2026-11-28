# p-adic monodromy theorem

Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete discretely valued field of
characteristic $0$ whose residue field $k$ is perfect of characteristic $p$; equivalently, a finite
extension of $K_0 = W(k)[1/p]$ (for instance a finite extension of $\mathbb{Q}_p$). A $p$-adic representation
of $G_K$ is de Rham if and only if it is potentially semistable: for every de Rham representation $V$ there is
a finite extension $K'/K$ in $\bar K$ such that $V|_{G_{K'}}$ is semistable. (The converse, that potentially
semistable representations are de Rham, is elementary.)

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
  paper. There $K$ is a finite totally ramified extension of $W(k)[1/p]$ for a perfect field $k$ of characteristic
  $p$ (§0.1).
- P. Colmez, "Espaces vectoriels de dimension finie et représentations de de Rham", Astérisque 319 (2008),
  117–186, <http://www.numdam.org/item?id=AST_2008__319__117_0>: §0.1, p. 117 ($F = W(k_F)[1/p]$ for a perfect
  field $k_F$ of characteristic $p$), and §0.2, p. 118: for $K$ a finite extension of $F$ and $V$ a
  $\mathbb{Q}_p$-representation of $\mathcal{G}_K$ of dimension $d$, $V$ is de Rham if
  $B_{\mathrm{dR}}^+[1/t] \otimes_{\mathbb{Q}_p} V \cong (B_{\mathrm{dR}}^+[1/t])^d$ as a $\mathcal{G}_K$-module,
  semistable if $B_{\mathrm{st}}^+[1/t] \otimes_{\mathbb{Q}_p} V \cong (B_{\mathrm{st}}^+[1/t])^d$, and potentially
  semistable if it is semistable as a representation of $\mathcal{G}_L$ for a finite extension $L$ of $K$;
  Théorème 0.1 ("Toute représentation de de Rham de $\mathcal{G}_K$ est potentiellement semi-stable"), with a proof
  that does not use $p$-adic differential equations.
- O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (preliminary version),
  <https://math.stanford.edu/~conrad/papers/notes.pdf>: Theorem 9.3.5, p. 148 ("A $p$-adic representation $V$ of
  $G_K$ is de Rham if and only if it is potentially semistable in the sense that $V$ is a semistable
  $G_{K'}$-representation for some finite extension $K'/K$"), attributed there to Berger and to
  André–Kedlaya–Mebkhout.
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §8.3.1, Theorem A and Remark 8.50 (the $p$-adic monodromy conjecture, first proved by Berger), for $K$ a
  $p$-adic field as in the standing assumption from Chapter 4 on (Preface; §1.1, Definition 1.16).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the theorem as `GlobalTheory.Published.DeRhamPotSemistable`.
