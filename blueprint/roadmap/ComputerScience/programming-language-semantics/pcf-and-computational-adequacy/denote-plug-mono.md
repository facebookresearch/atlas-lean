# Plugging into a PCF context is monotone in the denotation

Let $C$ be a one-hole context
that turns terms of type $A$ in context $\Gamma$ into terms of type $B$ in context $\Delta$, and
let $t$ and $u$ be terms of type $A$ in context $\Gamma$. Write $C[s]$ for the term obtained by
plugging a term $s$ into the hole of $C$, and $[\![ s ]\!]\,\eta$ for the denotation of a term $s$
in an environment $\eta$, ordered in the domain of its type. If
$[\![ t ]\!]\,\eta \le [\![ u ]\!]\,\eta$ for every environment $\eta$ for $\Gamma$, then
$[\![ C[t] ]\!]\,\eta \le [\![ C[u] ]\!]\,\eta$ for every environment $\eta$ for $\Delta$.
