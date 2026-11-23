# Composition of PCF substitutions

Write $t[\sigma]$ for the result of applying a
substitution $\sigma$ to a PCF term $t$. Let $\sigma$ be a substitution from a context $\Gamma$ to
a context $\Delta$ and $\tau$ a substitution from $\Delta$ to a context $\Xi$. For every PCF term
$t$ of type $A$ in context $\Gamma$, $t[\sigma][\tau] = t[\sigma']$, where $\sigma'$ is the
substitution from $\Gamma$ to $\Xi$ that sends each variable $x$ of $\Gamma$ to
$\sigma(x)[\tau]$.
