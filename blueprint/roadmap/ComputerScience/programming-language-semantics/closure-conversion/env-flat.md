# Flat closure environment

For a map $\mathrm{acc}$ from natural numbers to target terms
and a list $i_1, \dots, i_n$ of natural numbers, the flat environment is the target term
$(\mathrm{acc}(i_1), (\mathrm{acc}(i_2), \dots, (\mathrm{acc}(i_n), \mathsf{unit})\dots))$, which
packs $\mathrm{acc}(i)$ for each $i$ in the list, in order, as nested pairs ending in
$\mathsf{unit}$; the empty list gives $\mathsf{unit}$.
