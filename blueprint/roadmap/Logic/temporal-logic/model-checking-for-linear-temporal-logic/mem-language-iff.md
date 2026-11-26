# Tableau acceptance via initial, local and fairness conditions

An infinite word $w$ is accepted by the generalized Büchi tableau of an LTL formula $\varphi$ if
and only if there is a sequence $s_0, s_1, \dots$ of tableau states such that $s_0$ makes $\varphi$
true, each step from $s_n$ to $s_{n+1}$ on the letter $w_n$ is a tableau step, and the sequence is
fair: every until occurrence is false, or has its right-hand side true, at arbitrarily late
positions.
