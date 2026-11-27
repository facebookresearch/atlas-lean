# Extending a semantic environment by one variable

Given a semantic value $a$ of type $A$
in a context $\Delta$ and a semantic environment $\eta$ for $\Gamma$ in $\Delta$, the extended
environment is the semantic environment for the context $A :: \Gamma$ (the context $\Gamma$ with a
new innermost variable of type $A$) in $\Delta$ that sends the new innermost variable to $a$ and
sends the successor of each variable $x$ of $\Gamma$ to $\eta(x)$.
