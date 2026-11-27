# Subject reduction for Curry-style System F

If $\Gamma \vdash M : \tau$ in [Curry-style System F](curry-style-system-f.md) and $M$ β-reduces in one step to $M'$, then $\Gamma \vdash M' : \tau$.

The system is not closed under η-reduction: $x : a \to \forall b.\, (b \to b) \vdash \lambda y.\, x\, y : a \to b \to b$ holds, and $\lambda y.\, x\, y$ η-reduces to $x$, but
$x : a \to \forall b.\, (b \to b) \vdash x : a \to b \to b$ does not hold. The Church-style term behind the first typing is $\lambda y{:}a.\, x\, y\, b$, which is not an η-redex.

## Depends on

- [Curry-style System F](curry-style-system-f.md)
- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 12.5.3 (subject reduction), the remark before it, and Example 12.5.4 (failure of closure under η).
