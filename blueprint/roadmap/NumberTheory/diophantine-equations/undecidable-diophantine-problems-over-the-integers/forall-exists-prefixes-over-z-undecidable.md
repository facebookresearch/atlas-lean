# Diophantine sentences over the integers with prefixes ∀⁹∃³ and ∀¹⁰∃² are undecidable

There is no algorithm that decides, for an arbitrary polynomial $P$ with integer coefficients in twelve variables, whether $\forall z_1 \cdots \forall z_9 \, \exists x \exists y \exists z \; P = 0$ holds over $\mathbb{Z}$; the same holds for the prefix $\forall^{10} \exists^2$.

For quantifiers $\rho_1, \dots, \rho_n \in \{\forall, \exists\}$, say that *$\rho_1 \cdots \rho_n$ over $\mathbb{Z}$ is undecidable* when there is no algorithm that decides, for an arbitrary polynomial $P(x_1, \dots, x_n) \in \mathbb{Z}[x_1, \dots, x_n]$, whether the sentence

$$
\rho_1 x_1 \cdots \rho_n x_n \; \bigl( P(x_1, \dots, x_n) = 0 \bigr)
$$

is true, all variables ranging over $\mathbb{Z}$. Write $\forall^k$ and $\exists^k$ for blocks of $k$ equal quantifiers.

**Theorem (Sun).**

1. $\forall^9 \exists^3$ over $\mathbb{Z}$ is undecidable: there is no algorithm to test whether $\forall z_1 \cdots \forall z_9 \, \exists x \, \exists y \, \exists z \; [P(z_1, \dots, z_9, x, y, z) = 0]$ for an arbitrary polynomial $P$ in $12$ variables with integer coefficients.
2. $\forall^{10} \exists^2$ over $\mathbb{Z}$ is undecidable: there is no algorithm to test whether $\forall z_1 \cdots \forall z_{10} \, \exists x \, \exists y \; [Q(z_1, \dots, z_{10}, x, y) = 0]$ for an arbitrary polynomial $Q$ in $12$ variables with integer coefficients.

Conventions: the sentences have no free variables and no parameters; $P$ and $Q$ range over all integer polynomials in the stated numbers of variables. For comparison, Tung showed that $\forall^n \exists$ over $\mathbb{Z}$ is co-NP-complete for each $n$, hence decidable, and that $\forall^{27} \exists^2$ over $\mathbb{Z}$ is undecidable; the theorem lowers $27$ to $10$.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Sun first proves that every recursively enumerable set $\mathcal{A} \subseteq \mathbb{N}$ is represented in nine integer unknowns with one sign condition: there is $P_{\mathcal{A}}(z_0, z_1, \dots, z_9)$ with integer coefficients such that $a \in \mathcal{A}$ exactly when $P_{\mathcal{A}}(a, z_1, \dots, z_9) = 0$ for some integers $z_1, \dots, z_8$ and $z_9 \ge 0$. Take $\mathcal{A}$ recursively enumerable and not recursive. Negating gives, for $a \notin \mathcal{A}$, the statement that for all $z_1, \dots, z_9$ either $-z_9 - 1 \ge 0$ or $P_{\mathcal{A}}(a, z) \neq 0$. A lemma of the paper expresses $n \ge 0$ for an integer $n$ by the existence of $x \neq 0$ with $(3n - 1)x^2 + 1$ a square, and $P \neq 0$ by the existence of $x \neq 0$ with $P = x$, so the complement of $\mathcal{A}$ becomes $\forall z_1 \cdots \forall z_9 \, \exists x \neq 0 \, [\,1 - (3 z_9 + 4) x^2 \in \square \vee P_{\mathcal{A}}(a, z) = x\,]$, where $\square$ is the set of squares. Tung's identity $m \neq 0 \iff \exists x \exists y\,[m = (2x+1)(3y+1)]$ replaces $x \neq 0$ by two unknowns and merges the disjunction into one product equation, giving the prefix $\forall^9 \exists^3$. For $\forall^{10} \exists^2$, Sun's second representation, $a \in \mathcal{A}$ iff $Q_{\mathcal{A}}(a, z_1, \dots, z_{10}) = 0$ for some integers $z_1, \dots, z_9$ and $z_{10} \neq 0$, negates to $\forall z_1 \cdots \forall z_{10} \exists x \exists y\,[z_{10}(Q_{\mathcal{A}} - (2x+1)(3y+1)) = 0]$. Deciding these sentences would decide the nonrecursive set $\mathcal{A}$. The same paper proves the [11 unknowns theorem](h10-over-z-with-eleven-unknowns.md): $\exists^{11}$ over $\mathbb{Z}$ is undecidable. A good expansion links pages for Sun's two representation theorems for recursively enumerable sets (Theorem 1.1 of the source), for the lemma expressing $n \ge 0$ and $P \ne 0$ existentially, and for Tung's identity.

## Sources

- Zhi-Wei Sun, *Further results on Hilbert's tenth problem*, Sci. China Math. 64 (2021), no. 2, 281–306, https://doi.org/10.1007/s11425-020-1813-5, read in the copy arXiv:1704.03504v7: clauses 1 and 2 are Corollary 1.4 (i) and (ii) there, the representation theorems are Theorem 1.1 (i) and (ii), the proof is in Section 5, and the 11 unknowns theorem is Corollary 1.2 (i).
