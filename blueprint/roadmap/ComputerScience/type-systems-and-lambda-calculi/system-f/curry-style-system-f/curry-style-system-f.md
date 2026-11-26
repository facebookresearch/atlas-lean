# Curry-style System F

Types of System F are type variables $a, b, \dots$, arrows $\sigma \to \tau$ and universal types $\forall a.\, \sigma$. An environment $\Gamma$ is a finite set of declarations
$x : \sigma$ of distinct term variables, and $\mathrm{var}(\Gamma)$ is the set of type variables free in its types. Curry-style System F assigns types to
*pure* (untyped) λ-terms $M$ by the rules

- (Var) $\Gamma, x : \tau \vdash x : \tau$;
- (Abs) if $\Gamma, x : \sigma \vdash M : \tau$ then $\Gamma \vdash \lambda x.\, M : \sigma \to \tau$;
- (App) if $\Gamma \vdash M : \sigma \to \tau$ and $\Gamma \vdash N : \sigma$ then $\Gamma \vdash M\, N : \tau$;
- (Gen) if $\Gamma \vdash M : \sigma$ and $a \notin \mathrm{var}(\Gamma)$ then $\Gamma \vdash M : \forall a.\, \sigma$;
- (Inst) if $\Gamma \vdash M : \forall a.\, \sigma$ then $\Gamma \vdash M : \sigma[a := \tau]$ for every type $\tau$.

Quantifier rules leave the term unchanged, so polymorphism is implicit. A pure term $M$ has type $\tau$ in $\Gamma$ exactly when $M$ is the
[type erasure](../system-f-erasure-and-closing-environments/erase.md) $|M_0|$ of a [Church-style System F](../the-five-typing-rules-of-pure-system-f/typing.md) term $M_0$ with $\Gamma \vdash M_0 : \tau$, the erasure deleting type annotations,
type abstractions and type applications. For example $\lambda x.\, x\, x$ has type $(\forall a.\, a \to a) \to (\forall a.\, a \to a)$.

*Typability* asks, given $M$, whether $\Gamma \vdash M : \tau$ for some $\Gamma$ and $\tau$; *type checking* asks, given $\Gamma$, $M$ and $\tau$, whether $\Gamma \vdash M : \tau$.

## Depends on

- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)
- [Extrinsic typing of pure System F terms](../the-five-typing-rules-of-pure-system-f/typing.md)
- [Type erasure of System F terms to untyped terms](../system-f-erasure-and-closing-environments/erase.md)

## Sources

- A. Dudenhefner, "The undecidability of System F typability and type checking for reductionists", *Proceedings of the 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS)*, 2021, <https://ps.uni-saarland.de/Publications/documents/Dudenhefner_2021_SystemF.pdf>: Definitions 1–5 (terms, types, environments, Curry-style type assignment, typability) and Problems 6 and 7 (typability and type checking).
- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 12.5, Definition 12.5.1 (erasure) and Proposition 12.5.2 (Curry-style typings are erasures of Church-style ones).
