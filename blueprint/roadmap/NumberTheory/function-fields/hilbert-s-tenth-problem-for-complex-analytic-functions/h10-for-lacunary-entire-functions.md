# Hilbert's tenth problem is undecidable for rings of lacunary entire functions of finite order

Let $\mathcal{A}$ be a ring of complex entire functions of finite order that contains $\mathbb{C}[z]$ and consists of lacunary functions. Then the integers are positive existentially definable in $\mathcal{A}$ over the language of rings with a constant for $z$, so the analogue of Hilbert's tenth problem for $\mathcal{A}$ is undecidable.

An entire function $f$ of one complex variable has *finite order* when there is $A > 0$ with $\log \max\{|f(z)| : |z| \le r\} = O_f(r^A)$; these functions form a ring $\mathcal{H}_{\mathrm{fin}}$. A power series $\sum_{n \ge 0} a_n z^n$ is *lacunary* when for every $M \ge 1$ there is $N$ with $a_{N+1} = \cdots = a_{N+M} = 0$, and *holonomic* when it satisfies a linear differential equation $P_k F^{(k)} + \cdots + P_1 F' + P_0 F = 0$ with polynomial coefficients, $P_k \ne 0$; an entire function is lacunary or holonomic when its Taylor series at $0$ is. Polynomials are lacunary, holonomic and of finite order. A ring of entire functions containing $\mathbb{C}[z]$ is a structure for the language $\mathcal{L}_z = \{0, 1, z, +, \times, =\}$.

**Theorem (Garcia-Fritz–Pasten).**

1. Let $\mathcal{A} \subseteq \mathcal{H}_{\mathrm{fin}}$ be a ring containing $\mathbb{C}[z]$ whose holonomic elements are exactly the polynomials. Then $\mathbb{Z}$ is positive existentially definable in $\mathcal{A}$ over $\mathcal{L}_z$, and the positive existential theory of $\mathcal{A}$ over $\mathcal{L}_z$ is undecidable.
2. The same conclusion holds for every ring $\mathcal{A} \subseteq \mathcal{H}_{\mathrm{fin}}$ containing $\mathbb{C}[z]$ such that every element of $\mathcal{A}$ is lacunary: the analogue of Hilbert's tenth problem for $\mathcal{A}$, with coefficients in $\mathbb{Z}[z]$, is unsolvable.

Conventions: clause 1 with $\mathcal{A} = \mathbb{C}[z]$ is Denef's theorem; an example for clause 2 is the ring of $f \in \mathcal{H}_{\mathrm{fin}}$ whose number of nonzero Taylor coefficients of index at most $x$ is $O_{f,\varepsilon}(x^{\varepsilon})$ for every $\varepsilon > 0$, which contains transcendental functions such as $\sum_{n \ge 1} z^{n^n} / (n^n)!$. The source records that the case of the full ring of complex entire functions of one variable over $\mathcal{L}_z$ remains open.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Entire functions](../../../Analysis/complex-analysis/entire-functions/growth-of-entire-functions-along-continua/entire.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The key fact is that if $f, g \in \mathcal{H}_{\mathrm{fin}}$ satisfy the Pell equation $f^2 - (z^2 - 1) g^2 = 1$, then $f$ and $g$ are holonomic. In a ring whose holonomic elements are the polynomials, the solutions of this Pell equation are therefore exactly its polynomial solutions $(\pm x_n, \pm y_n)$, and Denef's argument for polynomial rings applies: the set $\{ y(1) : y \text{ a second coordinate of a solution} \}$ is $\mathbb{Z}$, and it is positive existentially definable over $\mathcal{L}_z$. Since the positive existential theory of $\mathbb{Z}$ is undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem, so is that of $\mathcal{A}$. A good expansion links pages for the holonomicity of Pell solutions of finite order (Theorem 1.3 of the source), for the fact that lacunary holonomic entire functions are polynomials, and for Denef's theorem for polynomial rings.

## Sources

- Natalia Garcia-Fritz and Hector Pasten, *Hilbert's tenth problem for lacunary entire functions of finite order*, Math. Log. Q. 70 (2024), no. 2, 205–209, https://doi.org/10.1002/malq.202300046, read in the copy arXiv:2308.05714v1: clause 1 is Theorem 1.1 and clause 2 Theorem 1.2 there, and the statement about Pell solutions is Theorem 1.3.
