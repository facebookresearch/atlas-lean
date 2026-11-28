# Context algebra of PCF

The typed context algebra whose judgments are all pairs $(\Gamma, A)$ of a typing context and a type, open contexts included. The terms at $(\Gamma, A)$ are the PCF terms of type $A$ in $\Gamma$; a context from $(\Gamma, A)$ to $(\Delta, B)$ is a typed one-hole context that takes a term of type $A$ in $\Gamma$ to a term of type $B$ in $\Delta$. Plugging the hole returns the term, and plugging a composite context applies the inner context first. A hole may therefore receive a term with free variables.
