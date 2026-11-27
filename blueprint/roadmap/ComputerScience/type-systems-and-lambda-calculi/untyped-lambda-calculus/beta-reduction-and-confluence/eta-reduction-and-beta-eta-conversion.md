# η-reduction and βη-conversion

A term $\lambda x.\, t\, x$ in which $x$ is not free in $t$ is an *η-redex*, with contractum $t$. *One-step η-reduction* $\to_\eta$ contracts one η-redex anywhere in a
term (it is the least relation compatible with abstraction and application containing $\lambda x.\, t\, x \to_\eta t$ for $x$ not free in $t$), and one-step
βη-reduction is the union of $\to_\beta$ and $\to_\eta$. *βη-reduction* $\twoheadrightarrow_{\beta\eta}$ is its reflexive–transitive closure, the least reflexive and transitive relation compatible with
the term formers that contains $(\lambda x.\, t)\, u \twoheadrightarrow_{\beta\eta} t[x := u]$ and $\lambda y.\, v\, y \twoheadrightarrow_{\beta\eta} v$ for $y$ not free in $v$, and *βη-conversion* $=_{\beta\eta}$ is the
least equivalence relation containing it. A term is *βη-normal* if it contains no β- or η-redex.

βη-reduction is preserved by substitution, and if $t \twoheadrightarrow_{\beta\eta} t'$ then every free variable of $t'$ is free in $t$. βη-conversion is extensional: if
$t\, u =_{\beta\eta} t'\, u$ for every term $u$, then $t =_{\beta\eta} t'$ (take $u$ a fresh variable and use an η-step).

## Depends on

- [β-reduction](beta-reduction.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 1, Section 4 (η-redexes, the relations $\eta_0$, $\beta\eta_0$, $\eta$ and $\beta\eta$, Propositions 1.29–1.31, βη-normal terms, the definition of $\simeq_{\beta\eta}$ and the extensionality remark after Proposition 1.35).
