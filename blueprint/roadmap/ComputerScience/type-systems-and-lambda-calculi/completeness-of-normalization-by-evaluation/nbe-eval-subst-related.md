# Evaluation after a substitution

Let $t$ be a term of type $A$ in a context $\Gamma$, let $\sigma$ be a substitution from $\Gamma$
to a context $\Delta$ and let $\eta$ be a [logical](logical-2.md) semantic environment for
$\Delta$ in a context $\Theta$. Then the evaluation in $\eta$ of $t$ with $\sigma$ applied is
[related](related.md) at type $A$ to the evaluation of $t$ in the environment that sends each
variable $x$ of $\Gamma$ to the evaluation of $\sigma(x)$ in $\eta$.
