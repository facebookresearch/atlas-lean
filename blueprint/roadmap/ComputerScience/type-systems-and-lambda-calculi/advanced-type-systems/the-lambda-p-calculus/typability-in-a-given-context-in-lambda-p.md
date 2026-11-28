# Typability of pure terms in a given context of λP is undecidable

It is undecidable whether an untyped λ-term can be decorated with type annotations so as to become a well-typed object of the λΠ-calculus (λP) in a given context; in the empty context the problem is decidable.

**λΠ-calculus.** Terms are $T ::= \mathit{Type} \mid \mathit{Kind} \mid x \mid (T\ T) \mid \lambda x{:}T.\, T \mid \Pi x{:}T.\, T$, typed in contexts $\Gamma$ by the rules of [λP](the-calculus-lambda-p.md) in the full λ-cube specification of Barendregt's presentation, with constructor abstractions (the linked page also describes a restricted raw grammar without them, which is not the one used here): $\vdash \mathit{Type} : \mathit{Kind}$, products $\Pi x{:}T.\, T'$ with $T : \mathit{Type}$ and $T' : s$, abstraction, application with substitution into the result type, and conversion modulo β (or βη). A term $t$ with $\Gamma \vdash t : T$ is an object in $\Gamma$ if $\Gamma \vdash T : \mathit{Type}$.

**Pure terms and typability.** Pure terms are $u ::= x \mid (u\ u) \mid \lambda x.\, u$. The content $|t|$ of an object erases type annotations: $|x| = x$, $|(t\ t')| = (|t|\ |t'|)$, $|\lambda x{:}U.\, t| = \lambda x.\, |t|$. A pure term $u$ is typable in a context $\Gamma$ if some extension $\Gamma\Delta$ of $\Gamma$ has an object $t$ with $u = |t|$: the bound variables and the free variables not declared in $\Gamma$ receive types, the others keep their types from $\Gamma$.

**Theorem.** The following problem is undecidable. Input: a context $\Gamma$ of the λΠ-calculus and a pure term $u$. Question: is $u$ typable in $\Gamma$?

## Depends on

- [The calculus λP](the-calculus-lambda-p.md)
- [β-reduction](../../untyped-lambda-calculus/beta-reduction-and-confluence/beta-reduction.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof uses the single context $\Gamma = [T : \mathit{Type};\ a, b : T \to T;\ c, d : T;\ P : T \to \mathit{Type};\ F : \Pi x{:}T.\,((P\ x) \to T)]$. Words over $\{A, B\}$ become terms $\hat\varphi$ of type $T \to T$ built from $a$ and $b$ (Huet's encoding), and $\tilde\varphi = |\hat\varphi|$. For a Post instance $\{\langle \varphi_1, \psi_1 \rangle, \dots, \langle \varphi_n, \psi_n \rangle\}$ the pure term $\lambda f.\lambda g.\lambda h.\,(f\ (g\ a \cdots a)\ (h\ (g\ \tilde\varphi_1 \cdots \tilde\varphi_n))\ (h\ (g\ \tilde\psi_1 \cdots \tilde\psi_n))\ (F\ c\ (g\ \lambda y.y \cdots \lambda y.y))\ (F\ d\ (g\ \lambda y.d \cdots \lambda y.d)))$ is typable in $\Gamma$ iff the instance has a solution: a type for $g$ must have the form $\Pi x_1{:}T \to T \cdots \Pi x_n{:}T \to T.\, (P\ (\delta\ x_1 \cdots x_n))$, and the constraints force the normal form of $\delta$ to be $\lambda x_1 \dots x_n.\, (x_{i_1} (\cdots (x_{i_p}\ c)))$ with $p > 0$ and $\varphi_{i_1} \cdots \varphi_{i_p} = \psi_{i_1} \cdots \psi_{i_p}$. In the empty context the typable pure terms are exactly the simply typable ones (Harper, Honsell and Plotkin; see [Curry-style λP types exactly the simply typable terms](curry-style-lambda-p-types-exactly-the-simply.md)), so typability there is decidable; that contrast is not used in the reduction. Typability with a given type, rather than a given context only, is the [type checking problem](type-checking-in-curry-style-lambda-p-is.md), also undecidable. A good expansion adds pages for Huet's encoding of words as terms of type $T \to T$ and for the source's Propositions 3 to 6, which characterize the types of $g$ and the normal form of $\delta$.

## Sources

- Gilles Dowek, "The undecidability of typability in the Lambda-Pi-calculus", *Typed Lambda Calculi and Applications (TLCA 1993)*, Lecture Notes in Computer Science 664, Springer, 139–145, 1993, <https://doi.org/10.1007/BFb0037103>; read as arXiv:2306.07599v1, <https://arxiv.org/abs/2306.07599v1>: the definitions of Section 2 (objects, pure terms, content, typability in a context) and the theorem of Section 4 with its proof.
