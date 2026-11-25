# Gödel's System T

System T extends the simply typed lambda calculus with a base type $\mathrm{nat}$, the constants $0 : \mathrm{nat}$ and $\mathrm{S} : \mathrm{nat} \to \mathrm{nat}$, and for every type $A$ a recursor $\mathrm{R}_A : A \to (\mathrm{nat} \to A \to A) \to \mathrm{nat} \to A$, with reduction rules $\beta$, $\mathrm{R}\,u\,v\,0 \to u$ and $\mathrm{R}\,u\,v\,(\mathrm{S}\,t) \to v\,t\,(\mathrm{R}\,u\,v\,t)$.

## Depends on

- [Typed de Bruijn variables of the simply typed lambda calculus](../simply-typed-lambda-calculus/var.md)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapter 7
