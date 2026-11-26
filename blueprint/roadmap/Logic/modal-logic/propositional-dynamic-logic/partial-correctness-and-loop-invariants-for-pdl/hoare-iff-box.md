# Hoare triples with formula assertions as box validity

For formulas $\varphi$ and $\psi$ and a program $a$ of PDL, the Hoare triple
$\{\varphi\}\, a\, \{\psi\}$ (with the sets of worlds where $\varphi$ and $\psi$ hold as assertions)
holds if and only if $\varphi \to [a]\psi$ holds at every world of the model.
