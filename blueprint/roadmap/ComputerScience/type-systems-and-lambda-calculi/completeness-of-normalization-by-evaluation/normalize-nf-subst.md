# The normal form after a substitution

Let $t$ be a term of type $A$ in a context $\Gamma$ and let $\sigma$ be a substitution from
$\Gamma$ to a context $\Delta$. The normal form computed by normalization by evaluation of $t$ with
$\sigma$ applied is the reification at type $A$ of the evaluation of $t$ in the environment that
sends each variable $x$ of $\Gamma$ to the evaluation of $\sigma(x)$ in the identity semantic
environment of $\Delta$.
