# Beta conversion of a closed Fω lambda application

For every environment $\sigma$ of model terms for $m$ term variables, type $A \in
\mathrm{Ty}^{\star}_{\Delta}$, $b \in \mathrm{Tm}_{\Delta,m+1}$ and model term $a$, the application
$(\lambda A.\,b)\{\sigma\}\,a$ is
[β-equivalent](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md) to $b\{a
\cdot \sigma\}$, where $a \cdot \sigma$ sends $0$ to $a$ and $i + 1$ to $\sigma(i)$
([closing](close.md)).
