# Evaluating a lifted substitution

Let $\sigma$ be a substitution from a context $\Gamma$ to a context $\Delta$, let $\eta$ be a
[logical](logical-2.md) semantic environment for $\Delta$ in a context $\Theta$, let $\rho$ be a
renaming from $\Theta$ to a context $\Omega$, and let $a$ and $b$ be [related](related.md)
semantic values of type $A$ in $\Omega$. Consider the environment for $\Gamma$ extended by $A$
that evaluates each term of the lift of $\sigma$ (which sends the new variable to itself and each
variable $x$ of $\Gamma$ to $\sigma(x)$ weakened) in the environment that sends the new variable
to $a$ and each variable $y$ of $\Delta$ to $\eta(y)$ renamed along $\rho$. It is
[related](related-2.md) to the environment that sends the new variable to $b$ and each variable
$x$ of $\Gamma$ to the evaluation of $\sigma(x)$ in $\eta$, renamed along $\rho$.
