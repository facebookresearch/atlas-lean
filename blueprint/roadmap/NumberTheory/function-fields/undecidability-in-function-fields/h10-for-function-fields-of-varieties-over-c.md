# Hilbert's tenth problem is undecidable for function fields of varieties of dimension at least two over algebraically closed fields of characteristic zero

Let $K$ be the function field of a variety of dimension at least $2$ over an algebraically closed field of characteristic zero. Then Hilbert's tenth problem for $K$ is undecidable, for polynomials with coefficients in a suitable finitely generated subring of $K$.

Let $k$ be an algebraically closed field of characteristic zero and let $K$ be the function field of an irreducible variety of dimension $n \ge 2$ over $k$, that is, a finite extension of a rational function field $k(t_1, \dots, t_n)$. Since $K$ may be uncountable, Hilbert's tenth problem for $K$ is taken with coefficients in a finitely generated subring $A \subseteq K$: it asks for an algorithm deciding whether a polynomial with coefficients in $A$ has a zero in $K^m$.

**Theorem (Eisenträger).**

1. Let $K$ be the function field of a variety of dimension at least $2$ over an algebraically closed field $k$ of characteristic zero. Then Hilbert's tenth problem for $K$ is undecidable.
2. For $K$ the function field of a surface over $k$, the coefficient ring can be taken to be $\mathbb{Z}[z_1, z_2]$ for suitable $z_1, z_2 \in K$ generating an extension of transcendence degree $2$ of $k$: Hilbert's tenth problem for $K$ with coefficients in $\mathbb{Z}[z_1, z_2]$ is undecidable.

Clause 1 is the main theorem of the research paper, and clause 2 is the precise form it proves for surfaces; the expository chapter states clause 2 for surfaces over $\mathbb{C}$. Conventions: the case $K = \mathbb{C}(t_1, t_2)$ is the theorem of Kim and Roush; for function fields of curves over $\mathbb{C}$, such as $\mathbb{C}(t)$, the problem is open.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof follows Kim and Roush's method for [$\mathbb{C}(t_1, t_2)$](h10-over-complex-rational-functions-in-two-variables.md): one builds in $K$ a Diophantine model of the structure $\langle \mathbb{Z} \times \mathbb{Z}, +, \mid, \mathcal{Z} \rangle$, whose positive existential theory is undecidable, using two quadratic twists $\mathcal{E}_1, \mathcal{E}_2$ of an elliptic curve without complex multiplication, of the form $(z_i^3 + a z_i + b) y^2 = x^3 + ax + b$. The new step is to find, in an arbitrary finite extension $L$ of $\mathbb{C}(t_1, t_2)$, elements $z_1, z_2$ generating a subfield of transcendence degree $2$ over $\mathbb{C}$ such that both twists have rank one over $L$, with known generators. A theorem of Moret-Bailly on elliptic curves over function fields gives such $z_1, z_2$; characteristic zero is used in this construction of rank-one curves. The source first treats surfaces over $\mathbb{C}$, notes that the proof is the same over any algebraically closed field of characteristic zero, and then extends it to varieties of higher dimension. A good expansion links pages for Moret-Bailly's theorem on elliptic curves over function fields (Theorem 5.2 of the expository chapter), for the rank-one twists it yields (Theorem 5.3 there), for the existential undecidability of the structure $\langle \mathbb{Z} \times \mathbb{Z}, +, \mid, \mathcal{Z} \rangle$, and for the transfer of undecidability along a Diophantine model.

## Sources

- Kirsten Eisenträger (Eisentraeger), *Hilbert's tenth problem for function fields of varieties over $\mathbb{C}$*, Int. Math. Res. Not. 2004, no. 59, 3191–3205, https://doi.org/10.1155/S1073792804141354, read in the copy arXiv:math/0609540v1 (numbering of that version): clause 1 is Theorem 1.2, the surface case is Theorem 1.1, and the coefficient ring $\mathbb{Z}[z_1, z_2]$ is specified in the paragraphs after each theorem.
- Kirsten Eisenträger (Eisentraeger), *Hilbert's tenth problem for function fields of characteristic zero*, in: Model Theory with Applications to Algebra and Analysis, Cambridge University Press, 2008, pp. 237–254, https://doi.org/10.1017/CBO9780511735219.008, read in the copy arXiv:math/0610162v1: clause 2 for surfaces over $\mathbb{C}$ is Theorem 5.1 there (numbering of that version), presented as established, and the existence of rank-one twists $\mathcal{E}_1, \mathcal{E}_2$ is Theorem 5.3.
