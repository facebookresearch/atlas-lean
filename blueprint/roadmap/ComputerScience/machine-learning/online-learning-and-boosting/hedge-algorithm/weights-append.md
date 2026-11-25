# A Hedge run splits at any round

For every learning rate $\eta$, sequences of rounds
$\lambda$ and $\lambda'$, and initial weights $w$, the weights after running Hedge on the rounds of
$\lambda$ followed by those of $\lambda'$, starting from $w$, equal the weights after running it on
$\lambda'$ starting from the weights reached after $\lambda$ from $w$.
