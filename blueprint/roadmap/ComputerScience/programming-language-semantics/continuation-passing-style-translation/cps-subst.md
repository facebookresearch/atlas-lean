# The CPS translation commutes with substitution of values and variables

Fix an answer
type $R$ and write $\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types,
contexts (entrywise) and terms; for a variable $x$ of $\Gamma$, $\llbracket x \rrbracket$ is the
variable of $\llbracket \Gamma \rrbracket$ at the same position. Let $\sigma$ be a substitution from
$\Gamma$ to $\Delta$ and $\tau$ a substitution from $\llbracket \Gamma \rrbracket$ to
$\llbracket \Delta \rrbracket$ such that for every variable $x$ of $\Gamma$, the term
$\tau(\llbracket x \rrbracket)$ is related to $\sigma(x)$ by the value translation $\Psi$ (a
variable is related to the corresponding variable, $\lambda y. N$ to
$\lambda y. \llbracket N \rrbracket$). Then for every term $M$ in $\Gamma$, writing $M[\sigma]$
for the result of applying $\sigma$ to $M$, we have
$\llbracket M[\sigma] \rrbracket = \llbracket M \rrbracket[\tau]$.
