# Packed accessors evaluate to an encoded related environment

Let $\rho$ be a list of
source values, $\rho_t$ a list of target values and $\mathit{acc}$ a map from natural numbers
to target terms, and suppose the accessors $\mathit{acc}$ implement $\rho$ in $\rho_t$: for
every $i < |\rho|$, the term $\mathit{acc}(i)$ evaluates in $\rho_t$ to a target value related
to $\rho_i$ by the value relation. Then there is a list $ws$ of target values with
$|ws| = |\rho|$ and $\rho_i$ related to $ws_i$ for every $i < |\rho|$, such that the target
term packing $\mathit{acc}(0), \dots, \mathit{acc}(|\rho| - 1)$ as nested pairs ending in
$\mathsf{unit}$ evaluates in $\rho_t$ to the encoding of $ws$ as nested pairs ending in the
unit value.
