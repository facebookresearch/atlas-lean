# Hodge–Tate representations

Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete discretely valued field of characteristic $0$ whose residue field is perfect of characteristic $p$ (for instance a finite extension of $\mathbb{Q}_p$), $C$ the completion of $\bar K$ and $C(i)$, $i \in \mathbb{Z}$,
its Tate twists. The **Hodge–Tate ring** is $B_{\mathrm{HT}} = \bigoplus_{i \in \mathbb{Z}} C(i) = C[t, t^{-1}]$,
graded, where $t$ denotes a basis of $\mathbb{Z}_p(1)$ and $G_K$ acts by $g(c t^i) = g(c) \chi(g)^i t^i$. It is
$(\mathbb{Q}_p, G_K)$-regular with $B_{\mathrm{HT}}^{G_K} = K$. A $p$-adic representation $V$ of $G_K$ (a
finite-dimensional $\mathbb{Q}_p$-vector space with a continuous linear action) is **Hodge–Tate** if it is
$B_{\mathrm{HT}}$-admissible, that is, if the graded $K$-vector space

$$D_{\mathrm{HT}}(V) = (B_{\mathrm{HT}} \otimes_{\mathbb{Q}_p} V)^{G_K} = \bigoplus_{i \in \mathbb{Z}} (C(i) \otimes_{\mathbb{Q}_p} V)^{G_K}$$

has dimension $\dim_{\mathbb{Q}_p} V$. Equivalently, $C \otimes_{\mathbb{Q}_p} V \cong \bigoplus_i C(i)^{h_i}$ for
integers $h_i \ge 0$, and then $h_i = \dim_K (C(-i) \otimes V)^{G_K}$, since $(C(j - i))^{G_K}$ is $K$ for $j = i$
and $0$ otherwise; these are the **Hodge–Tate numbers** of $V$ in Fontaine–Ouyang's convention. For
$V = \mathbb{Q}_p(1)$, $C \otimes V = C(1)$, so $h_1 = 1$.

**Sign conventions.** The literature on Galois representations attached to automorphic representations
uses the opposite sign. When $K$ is a finite extension of $\mathbb{Q}_p$, for a de Rham (in particular Hodge–Tate)
representation $W$ of $G_K$ on a
finite-dimensional $\overline{\mathbb{Q}}_p$-vector space and an embedding $\tau \colon K \to \overline{\mathbb{Q}}_p$,
the multiset $\mathrm{HT}_\tau(W)$ of **Hodge–Tate weights** contains $i$ with multiplicity
$\dim_{\overline{\mathbb{Q}}_p} (W \otimes_{\tau, K} C(i))^{G_K}$; so $\mathrm{HT}_\tau(\chi) = \{-1\}$, and the weights
of $W$ are the negatives of the Hodge–Tate numbers $i$ with $h_i \ne 0$, counted with multiplicity and
separated according to $\tau$.

## Depends on

- [Admissible representations for a regular ring of periods](admissible-representations.md), for $B$-admissibility
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for $C(i)$

## Proof depends on

- [Tate–Sen theorem on the Galois cohomology of C(i)](tate-sen-theorem.md), for $C^{G_K} = K$ and $C(i)^{G_K} = 0$ for $i \ne 0$, which give the regularity of $B_{\mathrm{HT}}$
- [Admissible representations for a regular ring of periods](admissible-representations.md)

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §6.1, Definition 6.1 ($B_{\mathrm{HT}}$), Proposition 6.2 (regularity), Definition 6.3, Proposition 6.4, the
  grading of $D_{\mathrm{HT}}(V)$ after Proposition 6.5, Definition 6.6 (Hodge–Tate numbers
  $h_i = \dim_K (C(-i) \otimes V)^{G_K}$) and Example 6.7.
- T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, "Potential automorphy and change of weight", Ann. of
  Math. 179 (2014), arXiv:1010.2561 (version 2), Notation, p. 8 (the multiset $\mathrm{HT}_\tau(W)$ "contains $i$
  with multiplicity $\dim_{\overline{\mathbb{Q}}_l} (W \otimes_{\tau, K} \widehat{\bar K}(i))^{G_K}$. Thus for example
  $\mathrm{HT}_\tau(\epsilon_l) = \{-1\}$").
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the second convention, with weights read off as jumps for an embedding, as `GlobalTheory.Pst.IsJumpsAt`.
