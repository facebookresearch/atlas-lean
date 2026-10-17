---
article_id: af_5c7f7bf91f655f39800df2e1
declaration: abbrev
origin: cited
statement: formalized
lean: CurveDiv
---

# Definition 23.13

To each point $P \in C(\bar{k})$ we associate a formal symbol $[P]$. The
 divisor group of $C$ is the free abelian group on the set $\{[P] \mid P \in
 C(\bar{k})\}$, denoted $\operatorname{Div} C$. Its elements are called
 divisors. Each is a finite sum of the form $D=\sum_{P} n_{P}[P]$ in which
 the $n_{P}$ are integers (so $n_{P}=0$ for all but finitely many $P$). The
 integer $n_{P}$ is the valuation of $D$ at $P$, also denoted by
 $v_{P}(D)\coloneqqn_{P}$. For each divisor $D$ the finite set
 $\operatorname{supp}(D)\coloneqq\{[P] \mid v_{P}(D) \neq 0\}$ is its
 support, and the integer $\operatorname{deg} D\coloneqq\sum_{P} v_{P}(D)$ is
 its degree. The degree map $D \mapsto \operatorname{deg} D$ is a surjective
 homomorphism of abelian groups whose kernel is the subgroup
 $\operatorname{Div}^{0} C$ of divisors of degree zero. Associated to each
 function $f \in k(C)^{\times}$ there is a divisor $\operatorname{div}
 f\coloneqq\sum_{P} v_{P}(f)[P]$, which is called a principal divisor.
 Because each $v_{P}: k(C)^{\times} \rightarrow \mathbb{Z}$ is a group
 homomorphism, we have $\operatorname{div} fg=\operatorname{div}
 f+\operatorname{div} g$, and the map $\operatorname{div}: k(C)^{\times}
 \rightarrow \operatorname{Div} C$ is a group homomorphism whose image
 $\operatorname{Princ} C$ is a subgroup of $\operatorname{Div} C$, and whose
 kernel consists of the nonzero constant functions $k^{\times}$, by Corollary
 23.10. The quotient group $\operatorname{Pic} C\coloneqq\operatorname{Div} C
 / \operatorname{Princ} C$ is the divisor class group or Picard group of $C$.
 Since $\operatorname{Princ} C$ lies in the kernel of the degree map $\deg:
 \operatorname{Div} C \rightarrow \mathbb{Z}$, we also have a degree map
 $\deg: \operatorname{Pic} C \rightarrow \mathbb{Z}$ on divisor classes, and
 its kernel is the group $\operatorname{Pic}^{0}
 C\coloneqq\operatorname{Div}^{0} C / \operatorname{Princ} C$ of divisor
 classes of degree zero. We then have an exact sequence $1 \longrightarrow
 k^{\times} \longrightarrow k(C)^{\times} \longrightarrow
 \operatorname{Div}^{0} C \longrightarrow \operatorname{Pic}^{0} C
 \longrightarrow 0$.

## Depends on

- [Definition 4.2](../../../part-01/section-4/section-4-1/036-definition-4-2.md)
- [Definition 23.4](../section-23-1/297-definition-23-4.md)

## Proof depends on

- [Corollary 23.10](../section-23-1/300-corollary-23-10.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 23.2](../../../../../../sources/v1/EllipticCurves.md)
