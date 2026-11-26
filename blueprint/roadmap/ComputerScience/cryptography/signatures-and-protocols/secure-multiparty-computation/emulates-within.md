# Quantitative one-exchange emulation

In charged gates, for each intermediary and upper clock
$t_A(k)$ for its whole run (including the return lookup), choose one simulator whose whole clock
is at most $\delta(t_A(k))$ at every parameter. For every environment, parameter, upper budget
$t_E$ for that environment (including the output lookup), and auxiliary string, the statistical
distance of the final **bit** laws must be strictly less than $\varepsilon(t_E)$. No monotonicity
of the two resource functions is assumed; the budget witnesses are not fed to any program.

## Sources

- one-exchange specialization of R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC Summer School (2025), slide 24.
