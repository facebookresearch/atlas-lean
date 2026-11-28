# The existential theory of the rational function field over a p-adic field is undecidable

For every finite extension $K$ of $\mathbb{Q}_p$, for any prime $p$ including $p = 2$, the valuation ring of the $t$-adic valuation is existentially definable in the rational function field $K(t)$, and consequently the existential theory of $K(t)$ is undecidable.

Let $p$ be a prime and let $K$ be a $p$-adic field, that is, a finite extension of $\mathbb{Q}_p$. Let $K(t)$ be the field of rational functions in one variable over $K$, and let $v_t$ be the $t$-adic valuation on $K(t)$. The *existential theory* of $K(t)$ is the set of existential sentences true in $K(t)$, in the language of rings with a constant symbol for $t$, the language of the criterion below. Its sentences are finite strings, so the problem has finite inputs; equivalently it asks whether finitely many polynomial equations with coefficients in $\mathbb{Z}[t]$ have a common solution in $K(t)$.

**Theorem (Degroote–Demeyer).**

1. The relation $v_t(x) \ge 0$ is Diophantine in $K(t)$: there is an existential formula, with parameters from $K$, defining $\{ x \in K(t) : v_t(x) \ge 0 \}$.
2. Consequently the existential theory of $K(t)$ is undecidable.

Conventions: clause 2 follows from clause 1 by a criterion of Denef in the form given by Pheidas and Zahidi: if an existential formula $\psi(x)$ holds for every $x \in K_0(t)$ with $v_t(x) \ge 0$, where $K_0$ is the prime field, and implies $v_t(x) \ge 0$ for every $x \in K(t)$, then the existential theory of $K(t)$ is undecidable. Kim and Roush had proved the undecidability for rational function fields over subfields of $p$-adic fields with $p$ odd; the new case is $p = 2$, and the theorem concerns $p$-adic fields themselves rather than their subfields.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [The p-adic numbers](../../p-adic-numbers/p-adic-numbers.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof works with quadratic forms over $K(t)$. Fix a uniformizer $\pi$ of $K$ and $\gamma \in K^{\times}$ such that the form $\langle 1, \pi \rangle \langle 1, -\gamma \rangle$ is anisotropic over $K$. Using a quadratic reciprocity symbol for polynomials over $K$ defined in the source, the authors prove isotropy over $K(t)$ for a class of quadratic forms, and show that when $v_t(f)$ is odd one of the two forms $\langle 1, \pi \rangle \langle 1, -\gamma, -t, -f \rangle$ and $\langle 1, \pi \rangle \langle 1, -\gamma, -t, -\gamma f \rangle$ is anisotropic over $K(t)$, while the isotropy theorem handles the case of even valuation. This gives an existential definition of "$v_t(x)$ is even" and from it of $v_t(x) \ge 0$; $K$ itself is Diophantine in $K(t)$, which takes care of the parameters. Denef's criterion then reduces Hilbert's tenth problem over $\mathbb{Z}$ to the existential theory of $K(t)$. A good expansion links pages for the Pheidas–Zahidi criterion (Theorem 1.1 of the source), for the isotropy and anisotropy results on the quadratic forms (Theorems 5.1 and 5.2), and for the existential definition of $v_t(x) \ge 0$ (Theorem 5.3 and Corollary 5.5).

## Sources

- Claudia Degroote and Jeroen Demeyer, *Hilbert's tenth problem for rational function fields over $p$-adic fields*, J. Algebra 361 (2012), 172–187, https://doi.org/10.1016/j.jalgebra.2012.03.039, read in the copy arXiv:1106.4912v1: clause 1 is Corollary 5.5 there, clause 2 is stated in its abstract and at the start of its Section 5, and the criterion is Theorem 1.1 of that version, quoted from Pheidas and Zahidi.
