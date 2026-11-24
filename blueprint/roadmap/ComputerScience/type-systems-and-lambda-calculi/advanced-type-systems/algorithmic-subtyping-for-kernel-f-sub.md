# Algorithmic subtyping for kernel F-sub

Types of $F_{<:}$ are type variables $x$, the maximal type $\top$, arrows $\sigma \to \tau$ and bounded quantifiers $\forall x{<:}\sigma.\, \tau$; contexts list bounds $x{<:}\tau$, and
$\Gamma[x]$ is the bound of $x$ in $\Gamma$. *Declarative* subtyping $\Gamma \vdash \sigma <: \tau$ has reflexivity, transitivity, $\Gamma \vdash \tau <: \top$, $\Gamma \vdash x <: \Gamma[x]$, the
arrow rule (contravariant in the domain, covariant in the codomain) and a rule for quantifiers. In *kernel* $F_{<:}$ the quantifier rule
requires equal bounds:

$$\frac{\Gamma, x{<:}\varphi \vdash \sigma <: \tau}{\Gamma \vdash \forall x{<:}\varphi.\, \sigma <: \forall x{<:}\varphi.\, \tau}.$$

*Algorithmic* subtyping $\Gamma \vdash_N \sigma <: \tau$ drops transitivity and general reflexivity and keeps: $\Gamma \vdash_N x <: x$; $\Gamma \vdash_N \tau <: \top$; $\Gamma \vdash_N x <: \tau$ if
$\Gamma \vdash_N \Gamma[x] <: \tau$; the arrow rule; and the kernel quantifier rule. Then:

- reflexivity and transitivity are admissible for $\vdash_N$, so $\Gamma \vdash_N \sigma <: \tau$ holds exactly when $\Gamma \vdash \sigma <: \tau$;
- the rules of $\vdash_N$ are syntax directed, and in kernel $F_{<:}$ the search they define terminates on every input, since the bounds in the
  context never change under a quantifier; hence kernel $F_{<:}$ subtyping is decidable.

In full $F_{<:}$, where the quantifier rule compares bounds contravariantly and rebinds the body with the smaller bound, the same algorithmic
system is still equivalent to the declarative one, but the search need not terminate, and subtyping is undecidable.

## Sources

- R. Álvarez Castro, *Mechanized Undecidability of Subtyping in System F*, Master's thesis, Saarland University, <https://ps.uni-saarland.de/~alvarez/thesis.pdf>: Section 1.1 (the kernel quantifier rule, Figure 1.2, and decidability of the kernel relation), Definition 5.1 and Section 5.1.1 (Definition 5.2 of the algorithmic system, Lemmas 5.3–5.4 and Theorem 5.5, stated there for the arrow-free fragment).
- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, Sections 28.3–28.5 (not opened; checked against Álvarez Castro, Sections 1.1 and 5.1.1).
- L. Cardelli and P. Wegner, "On understanding types, data abstraction, and polymorphism", *ACM Computing Surveys* 17(4):471–523, 1985 (not opened; origin of the kernel system as reported by Álvarez Castro, Section 1.1).
