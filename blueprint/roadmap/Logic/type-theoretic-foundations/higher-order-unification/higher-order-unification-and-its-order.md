# Higher-order unification and its order

Higher-order unification asks whether two terms of the simply typed λ-calculus with free variables become convertible after substituting terms for the variables. Its n-th-order version restricts the free variables to types of order at most n.

**Types and order.** Simple types are built from base types $\alpha$ by $A \to B$. The *order* of a type is $\operatorname{ord} \alpha = 1$ and $\operatorname{ord}(A \to B) = \max(\operatorname{ord} A + 1, \operatorname{ord} B)$. A term is *of order $n$* if all its free variables have types of order at most $n$ and all its constants have types of order at most $n + 1$.

**Problem.** An instance of *higher-order unification* is a typing context $\Gamma$ of free variables and two terms $s, t$ of the same type $A$ in the simply typed λ-calculus with constants. It is solvable if there are a context $\Delta$ and a substitution $\sigma$, assigning to each variable of $\Gamma$ a term of the same type in context $\Delta$, such that $s[\sigma]$ and $t[\sigma]$ are $\beta$-convertible:

$$
s[\sigma] \equiv_\beta t[\sigma].
$$

*$n$-th-order unification* is the same problem for terms of order $n$, with substitutions whose terms are of order $n$. First-order unification is the usual syntactic unification of first-order terms. Second-order unification is often stated for first-order terms over a signature extended with function variables, which stand for λ-abstractions over first-order terms.

## Depends on

- [β-reduction](../../../ComputerScience/type-systems-and-lambda-calculi/untyped-lambda-calculus/beta-reduction-and-confluence/beta-reduction.md)

## Proof depends on

None.

## Expansion

First-order unification is decidable (Robinson), even in linear time. Restricting the order of the substitution as well as of the terms does not change solvability: a unifier of two order-$n$ terms can be turned into one of order $n$. The source therefore reduces $n$-th-order unification to general higher-order unification.

## Sources

- S. Spies and Y. Forster, "Undecidability of higher-order unification formalised in Coq", in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 143–157, doi:[10.1145/3372885.3373832](https://doi.org/10.1145/3372885.3373832), read in the authors' open-access copy at <https://www.ps.uni-saarland.de/Publications/documents/SpiesForster_2019_UndecidabilityHOU.pdf>: Section 2 (higher-order unification) and Section 3 (order typing, Definition 3.3 of $n$-th-order unification and the reduction to general unification).
