# Weighted majority update

Given a penalty factor $\beta$ and weights $w_0, \dots, w_{n-1}$
in a field $K$, and a round with advice $a \in \{\mathrm{true}, \mathrm{false}\}^n$ and outcome
$y$, the updated weight of expert $i$ is $w_i$ if $a_i = y$ and $\beta w_i$ otherwise: after the
outcome is revealed, every expert that was wrong has its weight multiplied by $\beta$.
