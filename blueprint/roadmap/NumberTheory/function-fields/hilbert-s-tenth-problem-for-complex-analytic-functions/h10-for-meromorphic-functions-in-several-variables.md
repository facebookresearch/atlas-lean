# Hilbert's tenth problem is undecidable for meromorphic and entire functions of two complex variables with an evaluation predicate

In the field of meromorphic functions of two complex variables $z_1, z_2$, with constants for $z_1, z_2$ and a predicate for vanishing at the origin after setting $z_1 = 0$, the integers are positive-existentially definable, so the positive-existential theory is undecidable; the same holds for entire functions with a binary version of the predicate.

Let $\bar z = (z_1, z_2)$, let $\mathcal{H}_{\bar z}$ be the ring of entire functions on $\mathbb{C}^2$ and $\mathcal{M}_{\bar z}$ its field of fractions, the field of meromorphic functions on $\mathbb{C}^2$. For $f \in \mathcal{M}_{\bar z}$, let $\operatorname{eval}(f)$ mean: $f$ is defined at $z_1 = 0$, and its restriction to $z_1 = 0$ is an analytic function of $z_2$ that takes the value $0$ at $z_2 = 0$. For $a, b \in \mathcal{H}_{\bar z}$, let $\operatorname{eval}_0(a, b)$ mean $b \ne 0$ and $\operatorname{eval}(a / b)$. A *positive-existential* formula is built from atomic formulas by conjunction, disjunction and existential quantification.

**Theorem (Pheidas–Vidaux).**

1. The set $\mathbb{Z}$ of rational integers is positive-existentially definable in $\mathcal{M}_{\bar z}$ over the language of rings together with constant symbols for $z_1$ and $z_2$ and the unary predicate $\operatorname{eval}$.
2. The set $\mathbb{Z}$ is positive-existentially definable in $\mathcal{H}_{\bar z}$ over the language of rings together with constant symbols for $z_1$ and $z_2$ and the binary predicate $\operatorname{eval}_0$.

Consequently the positive-existential theory of each of these structures is undecidable: there is no algorithm to decide whether a system of polynomial equations with coefficients in $\mathbb{Z}[z_1, z_2]$, together with conditions $\operatorname{eval}(f)$ (respectively $\operatorname{eval}_0(a, b)$) on some unknowns, has a solution in $\mathcal{M}_{\bar z}$ (respectively $\mathcal{H}_{\bar z}$).

Conventions: the source's Theorem 2 proves a more general version for suitable subrings of meromorphic functions on connected subsets of $\mathbb{C}^m$, $m \ge 2$, over a language that also has symbols for the constant functions and for nonzero functions. The source notes that Hilbert's tenth problem for the ring of entire functions of one complex variable, over the language of rings with a constant for the variable, is not known to be decidable or undecidable.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The predicate $\operatorname{eval}$ is the condition attached to a place of $\mathcal{M}_{\bar z}$: restrict to the line $z_1 = 0$, then evaluate at $z_2 = 0$. The source uses it, together with the constants $z_1$ and $z_2$, to give a positive-existential definition of $\mathbb{Z}$ inside these rings of functions; for entire functions a quotient $a / b$ stands in for a meromorphic function, which is why the predicate becomes binary. Since the positive-existential theory of $\mathbb{Z}$ is undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem, so is that of each structure. For comparison, Raphael Robinson proved that the full first-order theory of the ring of entire functions of one complex variable is undecidable, and previously known undecidability results of this existential kind for rings of analytic or meromorphic functions all concerned non-Archimedean fields. A good expansion links pages for the source's Theorem 2 and the lemmas from which it follows (Lemmas 7 and 19 and Corollary 26 of the source), and for the transfer of undecidability along a positive existential definition of $\mathbb{Z}$.

## Sources

- Thanases Pheidas and Xavier Vidaux, *Hilbert's tenth problem for complex meromorphic functions in several variables*, Int. Math. Res. Not. IMRN 2022, no. 19, 15474–15504, https://doi.org/10.1093/imrn/rnab185, read in the copy arXiv:1711.09412v1: the statement is Theorem 1 there (numbering of that version), a special case of its Theorem 2; the predicates are defined in its introduction.
