# Kummer theory for abelian extensions of exponent dividing n

Let $n \ge 1$ and let $F$ be a field containing a primitive $n$-th root of unity (so the characteristic
of $F$ does not divide $n$), with a fixed algebraic closure $\Omega$. For a subgroup $B$ of $F^\times$
containing $F^{\times n}$ with finite index, write $F[B^{1/n}]$ for the smallest subfield of $\Omega$
containing $F$ and an $n$-th root of every element of $B$. Then

$$E \mapsto F^\times \cap E^{\times n}$$

is a bijection from the finite abelian extensions $E \subseteq \Omega$ of $F$ whose Galois group is killed
by $n$ onto the subgroups $B$ of $F^\times$ containing $F^{\times n}$ with finite index; its inverse is
$B \mapsto F[B^{1/n}]$, and if $E$ corresponds to $B$ then $[E : F] = (B : F^{\times n})$.

Equivalently, the finite abelian extensions of $F$ in $\Omega$ of exponent dividing $n$ correspond to the
finite subgroups of $F^\times / F^{\times n}$, the extension of degree $|B / F^{\times n}|$ being obtained
by adjoining the $n$-th roots of representatives of $B / F^{\times n}$. For such an $E$ with Galois group
$G$, the map sending $a = \alpha^n \in F^\times \cap E^{\times n}$ to the homomorphism
$\sigma \mapsto \sigma(\alpha)/\alpha$ is an isomorphism
$(F^\times \cap E^{\times n}) / F^{\times n} \to \mathrm{Hom}(G, \mu_n)$, where $\mu_n$ is the group of
$n$-th roots of unity in $F$.

Milne obtains this isomorphism from the cohomology sequence of
$1 \to \mu_n \to E^\times \xrightarrow{x \mapsto x^n} E^{\times n} \to 1$, which ends with
$H^1(G, E^\times) = 0$, [Hilbert's Theorem 90](multiplicative-hilbert-s-theorem-90.md) for the finite Galois
extension $E/F$ (Milne, *Fields and Galois Theory*, Theorem 5.23). He compares the degrees $[E : F]$
with the indices $(B : F^{\times n})$. In that comparison,
$\lvert \mathrm{Hom}(G, \mu_n) \rvert = \lvert G \rvert$ by
[finite abelian duality](../../GroupTheory/abelian-groups/dual-groups-of-finite-abelian-groups/finite-abelian-dual-iso.md):
$G$ is killed by $n$, and a choice of primitive $n$-th roots identifies $\mu_n$ with the group of
$n$-th roots of unity in $\mathbb C$.

## Sources

- J. S. Milne, *Fields and Galois Theory*, version 5.10 (2022),
  <https://www.jmilne.org/math/CourseNotes/FT.pdf>, Chapter 5, "Kummer theory": Theorem 5.30 (the
  statement, for "abelian extensions of exponent $n$", which includes the trivial extension
  corresponding to $B = F^{\times n}$) and the isomorphism before it; Theorem 5.23 (Hilbert's Theorem 90 in
  Noether's form, $H^1(G, E^\times) = 0$).
- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Appendix to Chapter VII, Theorem A.3 (the
  correspondence with the finite subgroups of $K^\times / K^{\times n}$).
