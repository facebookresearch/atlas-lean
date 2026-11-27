# The computational metalanguage and its interpretation

The *metalanguage* has types $\tau ::= A \mid 1 \mid \tau_1 \times \tau_2 \mid T\tau$ over base types $A$, and terms built from variables, $*$, pairs, projections, function symbols of a
signature, $[e]_T : T\tau$ for $e : \tau$, and $\Gamma \vdash (\mathrm{let}_T\ x \Leftarrow e_1\ \mathrm{in}\ e_2) : T\tau_2$ for $\Gamma \vdash e_1 : T\tau_1$ and $\Gamma, x : \tau_1 \vdash e_2 : T\tau_2$. Its equational theory has
the rules of many-sorted equational logic, the η-rule for $1$, the β- and η-rules for $\times$, congruence for $[-]_T$ and $\mathrm{let}_T$, and

- (ass) $\mathrm{let}_T\ x_2 \Leftarrow (\mathrm{let}_T\ x_1 \Leftarrow e_1\ \mathrm{in}\ e_2)\ \mathrm{in}\ e_3 = \mathrm{let}_T\ x_1 \Leftarrow e_1\ \mathrm{in}\ (\mathrm{let}_T\ x_2 \Leftarrow e_2\ \mathrm{in}\ e_3)$, in a context $\Gamma$
  with $\Gamma \vdash e_1 : T\tau_1$, $\Gamma, x_1 : \tau_1 \vdash e_2 : T\tau_2$ and $\Gamma, x_2 : \tau_2 \vdash e_3 : T\tau_3$, the bound variables $x_1, x_2$ being distinct and not declared in $\Gamma$ (so $x_1$ is not free in $e_3$);
- (T.β) $\mathrm{let}_T\ x \Leftarrow [e_1]_T\ \mathrm{in}\ e_2 = e_2[e_1/x]$; (T.η) $\mathrm{let}_T\ x \Leftarrow e\ \mathrm{in}\ [x]_T = e$.

An *interpretation* in a category with finite products and a [strong monad](strong-monads.md) $(T, \eta, \mu, t)$ sends types to objects ($T\tau$ to $T[\![\tau]\!]$), contexts to
products, and a term in context $\Gamma$ to a morphism from $[\![\Gamma]\!]$, with $[\![\, [e]_T ]\!] = [\![e]\!] ; \eta$ and
$[\![\mathrm{let}_T\ x \Leftarrow e_1\ \mathrm{in}\ e_2]\!] = \langle \mathrm{id}, [\![e_1]\!] \rangle ; t ; [\![e_2]\!]^*$; an equation holds when both sides denote the same morphism.

## Depends on

- [Strong monads](strong-monads.md)

## Sources

- E. Moggi, "Notions of computation and monads", *Information and Computation* 93(1):55–92, 1991, <https://doi.org/10.1016/0890-5401(91)90052-4>: Section 3.1, Definition 3.7 with Tables 8, 9 and 10 (types, terms and inference rules of the metalanguage).
