# Rigidity of finitely axiomatized linear-regular theories is undecidable

Whether a finite set of linear-regular equations defines a rigid equational theory, one in which no term is provably equal to a nontrivial permutation of its own variables, is undecidable. Rigid theories correspond to polynomial monads, so this property cannot be decided from a finite presentation.

**Linear-regular and rigid theories.** An equational theory $T = (L, A)$ has a set $L$ of function symbols of given arities and a set $A$ of equations between terms in a context $x_1, \dots, x_n$; provability $A \vdash s = t$ is provability in equational logic. A term in context is *linear-regular* if every variable of the context occurs in it exactly once, and an equation is linear-regular if both its sides are. $T$ is *linear-regular* if all its consequences follow from its linear-regular consequences (in particular, if it has a linear-regular set of axioms). A linear-regular term $t(x_1, \dots, x_n)$ is *flabby* in $T$ if

$$
T \vdash t(x_1, \dots, x_n) = t(x_{\sigma(1)}, \dots, x_{\sigma(n)})
$$

for some permutation $\sigma \neq \mathrm{id}$ of $\{1, \dots, n\}$, and a linear-regular theory is *rigid* if it has no flabby terms.

**Theorem (Bojańczyk, Szawiel and Zawadowski).** The problem whether an equational theory $T = (L, A)$ with a finite language $L$ and a finite set $A$ of linear-regular axioms is rigid is undecidable (Theorem 3.1).

For example, the theories of monoids and of monoids with an anti-involution are rigid, while the theory of commutative monoids is not, since its axiom $m(x_1, x_2) = m(x_2, x_1)$ makes $m(x_1,x_2)$ flabby (Section 1).

## Depends on

- [Equational calculus](equational-calculus.md)

## Proof depends on

- [The uniform word problem for Thue systems is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-thue-wp.md)

## Expansion

The proof reduces the word problem for finitely presented monoids: for an instance $\bigwedge_i u_i = v_i \vdash u = v$ over a finite alphabet, one builds a finite linear-regular theory $T$ that is rigid iff the implication fails. It starts from the rigid theory $T_0$, which has three binary symbols $l, r, m$ and the single axiom $l(x_1, x_2) = r(x_2, x_1)$, and $T$ extends it. If the implication holds, an evident flabby term exists. Conversely, a linear-regular interpretation $I : T_0 \to T$ is conservative when the implication fails, and a map sending every term of $T$ to a "special" term in the image of $I$, preserving the order of variables and provable equality, transfers any flabby term of $T$ to a flabby term of $T_0$, which is impossible.

## Sources

- M. Bojańczyk, S. Szawiel and M. Zawadowski, "Rigidity is undecidable", *Mathematical Structures in Computer Science* 24(6), 2014, article e240605, doi:10.1017/S096012951300087X; read as arXiv:1204.4906v1, <https://arxiv.org/abs/1204.4906v1>: Section 1 (examples), Section 2 (equational theories, linear-regular and rigid theories), Theorem 3.1 and its proof sketch in Section 3 of arXiv:1204.4906v1.
