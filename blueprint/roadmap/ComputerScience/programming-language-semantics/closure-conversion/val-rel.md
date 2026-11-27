# Value relation for closure conversion

The relation between source values and target
values of closure conversion is the least relation such that, for every source lambda body $b$,
every list $\rho$ of source values and every list $ws$ of target values with $|\rho| = |ws|$
and $\rho_i$ related to $ws_i$ for every $i < |\rho|$, the source closure of $b$ over $\rho$ is
related to the target pair $(\mathsf{code}\,c, E)$. Here $c$ is the closure conversion of $b$ in
a scope of $|\rho| + 1$ variables with the code accessors, which read variable $0$ as
$\mathsf{fst}\,\#0$ and variable $i + 1$ as $\mathsf{fst}\,(\mathsf{snd}^i\,(\mathsf{snd}\,\#0))$,
where $\#0$ is the code parameter and $\mathsf{snd}^i$ applies the second projection $i$ times;
and $E$ is the encoding of $ws$ as nested pairs ending in the unit value.
