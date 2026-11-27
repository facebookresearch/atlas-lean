# The calculus λP

λP is the system of the λ-cube with sorts $*$ and $\square$, the axiom $* : \square$ and the rules $(*, *)$ and $(*, \square)$, as a
[pure type system](../pure-type-systems-and-the-calculus-of.md): types may depend on terms, but there is no quantification over types. The pages in this folder use a
restricted presentation without λ-abstractions in constructors, in which every constructor has the form $(\forall x_1{:}\tau_1) \cdots (\forall x_n{:}\tau_n)\, \alpha\, M_1 \cdots M_k$;
the full system of the cube also has constructor abstractions, for example $\lambda x{:}A.\, A$ in the context $A : *$. Dependent types in normal form have the
restricted shape, and substituting terms never creates a constructor redex. The raw expressions of the restricted presentation are

$$\Gamma ::= \{\} \mid \Gamma, (x : \varphi) \mid \Gamma, (\alpha : \kappa), \qquad \kappa ::= * \mid (\Pi x{:}\varphi)\kappa, \qquad
\varphi ::= \alpha \mid (\forall x{:}\varphi)\varphi \mid \varphi\, M, \qquad M ::= x \mid M\, M \mid \lambda x{:}\varphi.\, M,$$

with kinds $\kappa$, type constructors $\varphi$ and Church-style terms $M$; β-reduction acts in terms and, through the terms they contain, in constructors
and kinds. The typing rules assign kinds to constructors and types to terms; the type of $\lambda x{:}\tau.\, M$ is $(\forall x{:}\tau)\sigma$ when $M : \sigma$, application
substitutes the argument into the result type, and a conversion rule identifies β-equal types.

Under the propositions-as-types reading, λP expresses the fragment of many-sorted first-order intuitionistic logic with $\forall$ and $\to$:
$(\forall x{:}\tau)\sigma$ is universal quantification over the objects of type $\tau$, and implication is the case in which $x$ does not occur in $\sigma$; other
connectives need extensions of the system.

## Depends on

- [Pure type systems and the calculus of constructions](../pure-type-systems-and-the-calculus-of.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Chapter 10, Definition 10.1.1 (raw expressions and β-reduction), Remark 10.1.2 (no λ-abstractions in constructors), the typing rules of Section 10.2 and Definition 10.2.2; Example 13.6.1 (λP as a system of the λ-cube); Section 10.6 and Example 10.6.1 (λP and first-order logic, and the extension for existential quantification).
