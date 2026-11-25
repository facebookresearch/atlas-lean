# Completed evaluation on cycles

Let $k$ be a perfect field, $X$ a smooth proper $k$-scheme, $a \in \mathrm{Br}(X)$ and $n$ a
positive integer with $n a = 0$. For every zero-cycle $c$ on $X$ with integer coefficients,
`completed_zero_cycle_evaluation` sends the image of the class of $c$ in
$\varprojlim_m \mathrm{CH}_0(X)/m$ to `cycleEvaluation` of $c$, for the field comparisons
`source_field_gm_comparison` and the residue-field data `source_residue_field_data`.
