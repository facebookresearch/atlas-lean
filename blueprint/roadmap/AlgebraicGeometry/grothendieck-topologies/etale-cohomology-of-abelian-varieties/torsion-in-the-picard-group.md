# Torsion in the Picard group of an abelian variety

Let $A$ be an [abelian variety](../../abelian-varieties/abelian-scheme.md) of dimension $g$ over a separably closed field
$k$, with [dual abelian variety](../../abelian-varieties/dual-abelian-variety.md) $A^\vee$, and let $n \ge 1$ be an integer
not divisible by the characteristic of $k$. Write $\operatorname{Pic}(A)_n$ for the subgroup of
elements of $\operatorname{Pic}(A)$ killed by $n$. Then $\operatorname{Pic}(A)_n$ is contained in
$\operatorname{Pic}^0(A)$, and
$\operatorname{Pic}(A)_n = \operatorname{Pic}^0(A)_n = A^\vee_n(k)$ has exactly $n^{2g}$ elements.

For a line bundle $L$ on $A$, $L$ lies in $\operatorname{Pic}^0(A)$ exactly when the homomorphism
$\varphi_L \colon A \to A^\vee$, $a \mapsto t_a^* L \otimes L^{-1}$, is zero, and
$\varphi_{L \otimes M} = \varphi_L + \varphi_M$. If $L^{\otimes n}$ is trivial, then
$n \varphi_L = \varphi_{L^{\otimes n}} = 0$, so $\varphi_L = 0$ because
$\operatorname{Hom}(A, A^\vee)$ is torsion-free; this is the torsion-freeness of the Néron–Severi
group $\operatorname{Pic}(A) / \operatorname{Pic}^0(A)$, which $L \mapsto \varphi_L$ embeds in
$\operatorname{Hom}(A, A^\vee)$ (Milne, proof of Corollary I.10.18). Then
$\operatorname{Pic}^0(A) = A^\vee(k)$, and $A^\vee$ is an abelian variety of dimension $g$, whose
$n$-torsion over the separably closed field $k$ has $n^{2g}$ points.

## Depends on

- [Abelian scheme](../../abelian-varieties/abelian-scheme.md), for abelian varieties over a field
- [Dual abelian variety](../../abelian-varieties/dual-abelian-variety.md), for $\operatorname{Pic}^0(A)$ and $A^\vee$

## Proof depends on

- [Dual abelian variety](../../abelian-varieties/dual-abelian-variety.md), for $A^\vee(k) = \operatorname{Pic}^0(A)$ and
  $\dim A^\vee = \dim A$ (its item 1), and for $\varphi_L$ (its item 2)
- [Homomorphisms of abelian varieties are determined by their action on Tate modules](homomorphisms-of-abelian-varieties-and-tate-modules.md),
  for the torsion-freeness of $\operatorname{Hom}(A, A^\vee)$ (its item 2)
- [Isogenies of abelian schemes](../../abelian-varieties/isogenies-of-abelian-schemes.md), for the $n^{2g}$ points of
  $A^\vee$ killed by $n$ (its item 3)

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 7.3, p. 34; Proposition 8.4 and the definition of
  $\operatorname{Pic}^0(A)$ after it, pp. 35–36; Remark 8.7, p. 37; Lemma 10.6, p. 45; Corollary 10.18
  and its proof, p. 50.
