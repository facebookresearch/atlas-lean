# Subgroups containing a norm group are norm groups

Let $K$ be a number field with idèle class group $C_K$. A subgroup of $C_K$ is a norm group if it is
$\mathrm{Nm}_{L/K}(C_L)$ for some finite abelian extension $L/K$, where $\mathrm{Nm}_{L/K} \colon C_L \to C_K$
is induced by the idèle norm $\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$. If $U$ is
a norm group and $V$ is a subgroup of $C_K$ containing $U$, then $V$ is a norm group: if
$U = \mathrm{Nm}_{L/K}(C_L)$, then $V = \mathrm{Nm}_{M/K}(C_M)$ for the subfield $M$ of $L$ fixed by the
image of $V$ under the global Artin map of $L/K$.

Milne's proof: by the [global reciprocity law](../reciprocity-law/global-reciprocity-law.md), the Artin
map gives an isomorphism $C_K / U \to \mathrm{Gal}(L/K)$, which carries $V/U$ onto $\mathrm{Gal}(L/M)$; the
kernel of $C_K \to \mathrm{Gal}(L/K) \to \mathrm{Gal}(M/K)$ is therefore $V$. This composite is the global
Artin map of $M/K$, by its [compatibility with restriction](../reciprocity-law/global-artin-map.md), and
its kernel is $\mathrm{Nm}_{M/K}(C_M)$ by the reciprocity law for $M/K$.

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)
- [Global Artin map](../reciprocity-law/global-artin-map.md), for the description of $M$; the proof also uses its compatibility with restriction

## Proof depends on

- [Global reciprocity law](../reciprocity-law/global-reciprocity-law.md), for $L/K$ and for $M/K$

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Lemma VII.9.1 (the statement) and its proof; the
  definition of a norm group after Theorem V.5.5.
