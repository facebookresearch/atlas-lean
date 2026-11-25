# The call-by-name CPS translation at base types

Fix an answer type $R$ and an
interpretation of the base types. Let $t$ be a term of a base type $b$ in a context $\Gamma$, let
$\eta$ be an environment for $\Gamma$, and let $\eta'$ be an environment for the translated
context related to $\eta$. Then for every continuation $k$ from the values of type $b$ to the
values of type $R$, the denotation in $\eta'$ of the call-by-name CPS translation $\overline{t}$
of $t$, applied to $k$, equals $k$ applied to the denotation of $t$ in $\eta$.
