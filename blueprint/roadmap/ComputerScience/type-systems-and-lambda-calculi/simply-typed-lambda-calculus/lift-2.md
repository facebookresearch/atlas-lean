# Lifting a renaming under a binder

Let $\rho$ be a renaming from a context $\Gamma$ to a
context $\Delta$ and let $A$ be a simple type, and write $A :: \Gamma$ for the context obtained
by prepending $A$ to $\Gamma$. The lift of $\rho$ is the renaming from $A :: \Gamma$ to
$A :: \Delta$ that sends the variable $0$ to $0$ and sends the successor of a variable $x$ of
$\Gamma$ to the successor of $\rho(x)$.
