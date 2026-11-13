# Weakest liberal precondition unfolding of a while loop

Let $b$ be a Boolean expression,
$c$ a command and $Q$ an assertion. Write $\mathrm{wlp}(d, R)$ for the weakest liberal
precondition of a command $d$ with respect to an assertion $R$, and let $W$ be the loop
$\mathbf{while}\ b\ \mathbf{do}\ c$. Then $\mathrm{wlp}(W, Q)$ is the assertion that holds in a
state $s$ exactly when both of the following hold: if $b$ evaluates to false in $s$, then $Q$
holds in $s$; and if $b$ evaluates to true in $s$, then $\mathrm{wlp}(c, \mathrm{wlp}(W, Q))$
holds in $s$.
