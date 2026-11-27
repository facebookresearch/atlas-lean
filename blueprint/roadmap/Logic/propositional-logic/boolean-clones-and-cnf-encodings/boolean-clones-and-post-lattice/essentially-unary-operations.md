# Essentially unary operations

A Boolean operation $f : \{0,1\}^n \to \{0,1\}$ is *essentially unary* if it depends on at most one coordinate: there are $i \in [n]$ and $g : \{0,1\} \to \{0,1\}$ with $f(x) = g(x_i)$ for all $x$. The essentially unary operations are the projections, the negated projections and the constant operations of positive arity. The four special Boolean operations are $\wedge$ (binary conjunction), $\vee$ (binary disjunction), the ternary *majority* $\mathrm{maj}(x,y,z)$ and the ternary *minority* $x \oplus y \oplus z$.

## Depends on

- [Boolean clones](boolean-clones.md)

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
