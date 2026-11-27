# The λΔ-calculus

The terms of the type-free *λΔ-calculus* are $M ::= x \mid \lambda x.\, M \mid M\, M' \mid \Delta x.\, M$, where $\Delta x$ binds $x$. Its simply typed version has the implicational
formulas over propositional variables and $\bot$ as types, writes $\neg\varphi$ for $\varphi \to \bot$, and extends the Curry-style rules of the simply typed λ-calculus by the rule
for double-negation elimination

$$\frac{\Gamma, x : \neg\varphi \vdash M : \bot}{\Gamma \vdash \Delta x.\, M : \varphi}$$

(in the Church-style variant, $\Delta x{:}\neg\varphi.\, M$). Computationally, $\Delta$ is a control operator, akin to Scheme's call/cc.

*Δ-reduction* $\to_\Delta$ is the least compatible relation containing, on Church-style terms,

- $(\Delta x{:}\neg(\varphi \to \psi).\, M)\, N \to_\Delta \Delta z{:}\neg\psi.\, M\{x := \lambda y{:}\varphi \to \psi.\, z\, (y\, N)\}$;
- $\Delta x{:}\neg\varphi.\, x\, M \to_\Delta M$ if $x$ is not free in $M$;
- $\Delta x{:}\neg\varphi.\, x\, (\Delta y{:}\neg\varphi.\, N) \to_\Delta \Delta z{:}\neg\varphi.\, N\{x, y := z\}$;

and $\to_{\beta\Delta}$ is the union of β- and Δ-reduction.

## Depends on

- [β-reduction](../../untyped-lambda-calculus/beta-reduction-and-confluence/beta-reduction.md)
- [Simple type assignment à la Curry](../../simply-typed-lambda-calculus/decision-problems-for-simple-types/simple-type-assignment-a-la-curry.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 8.3, Definition 8.3.2 and Remark 8.3.3; Section 8.4, Definition 8.4.1; Section 8.7 for the reading of $\Delta$ as a control operator.
