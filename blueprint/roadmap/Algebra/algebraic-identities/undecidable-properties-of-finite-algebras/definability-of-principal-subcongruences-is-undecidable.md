# Definability of principal subcongruences is undecidable for finite algebras

No algorithm decides, for a finite algebra of finite type, whether the variety it generates has definable principal subcongruences; for Moore's algebras this property, finite basedness and the halting of a Turing machine coincide.

A *congruence formula* of a type $\tau$ is an existential positive formula $\psi(w, x, y, z)$ such that in every algebra $A$ of type $\tau$, $A \models \psi(a, b, c, d)$ implies $(a, b) \in \operatorname{Cg}^A(c, d)$. A class $\mathcal{C}$ of algebras of type $\tau$ has *definable principal subcongruences* (DPSC) if there are congruence formulas $\Gamma$ and $\psi$ such that for every $A \in \mathcal{C}$ and all $a \ne b$ in $A$ there are $c \ne d$ in $A$ with $A \models \Gamma(c, d, a, b)$ and

$$
\operatorname{Cg}^A(c, d) = \{(r, s) \in A^2 : A \models \psi(r, s, c, d)\}.
$$

**Theorem (Moore).** For every Turing machine $T$ there is a finite algebra $A'(T)$ of finite type, constructed effectively from $T$ by adding one operation to McKenzie's algebra $A(T)$, such that the following are equivalent:

1. $T$ halts;
2. $\mathcal{V}(A'(T))$ has definable principal subcongruences;
3. $A'(T)$ is finitely based.

Consequently there is no algorithm that decides, given a finite algebra $A$ of finite type, whether $\mathcal{V}(A)$ has definable principal subcongruences, and none that decides whether $A$ is finitely based.

Conventions: Turing machines are given by finite lists of instructions, and $T$ halts means that it halts when started on the empty tape, as in McKenzie's construction; the input algebra is given by the tables of its finitely many operations. The second consequence is a new proof of McKenzie's negative answer to Tarski's finite basis problem.

## Depends on

- [Varieties of algebras and finitely generated varieties](varieties-of-algebras-and-finitely-generated-varieties.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

McKenzie's algebra $A(T)$ has residual bound $\kappa(\mathcal{V}(A(T))) < \omega$ exactly when $T$ halts, and Moore checks that the extra operation preserves this. If $T$ halts, a long case analysis of the polynomials of $A'(T)$ shows that the finitely many finite subdirectly irreducible members of $\mathcal{V}(A'(T))$ admit uniform congruence formulas, so the variety has DPSC; by the Baker–Wang theorem, a variety with DPSC whose subdirectly irreducible members form a finitely axiomatizable class (here a finite set of finite algebras) is finitely based. If $T$ does not halt, an infinite subdirectly irreducible algebra $S_\omega$ lies in the variety, an ultrapower argument shows that the class of finitely subdirectly irreducible members is not axiomatizable, while DPSC would axiomatize it by one sentence; and the algebra $S_{\mathbb{Z}}$ containing $S_\omega$, which McKenzie used to show that $A(T)$ is inherently nonfinitely based when $T$ does not halt, lies in $\mathcal{V}(A'(T))$ as well. Since the halting problem is undecidable and $T \mapsto A'(T)$ is computable, both properties are undecidable.

A good expansion adds and links pages for McKenzie's construction of $A(T)$ and the computation of its residual bound, the Baker–Wang finite basis theorem for varieties with DPSC, and the non-axiomatizability of finitely subdirectly irreducible members when $T$ does not halt.

## Sources

- Matthew Moore, *The undecidability of the definability of principal subcongruences*, The Journal of Symbolic Logic 80 (2015), no. 2, 384–432, https://doi.org/10.1017/jsl.2014.51; Theorem 7.1 of arXiv:1301.5588v3, assembled from Theorem 5.26, Corollary 5.28 and Corollary 6.2 there; the definition of DPSC is in Section 1.
- Ralph McKenzie, *Tarski's finite basis problem is undecidable*, International Journal of Algebra and Computation 6 (1996), no. 1, 49–104, https://doi.org/10.1142/S0218196796000040, for the first negative answer to Tarski's problem, as cited in the paper above.
