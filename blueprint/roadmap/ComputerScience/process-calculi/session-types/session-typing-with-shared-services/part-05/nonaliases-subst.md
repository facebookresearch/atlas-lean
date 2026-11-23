# Nonshared endpoint substitution keeps owned names nonshared

Let $\Gamma$ be a service environment, $\Delta$ an ownership context separated from $\Gamma$ and $b$
a name that is not $\mathrm{c}_s$ for any $s$ declared in $\Gamma$. Then the name substitution $x
\mapsto x\{b/0\}$ (sending $\mathrm{v}_0$ to $b$, $\mathrm{v}_{i+1}$ to $\mathrm{v}_i$ and fixing
constants) sends no endpoint name of $\Delta$ to a declared trigger.
