# Security for a policy

A machine is secure for a relation $\rightsquigarrow$ on domains
(`policy`) if, for every action sequence $\alpha$ and action $a$, the output of $a$ after running
$\alpha$ from the initial state $s_0$ equals its output after running
$\mathrm{purge}(\alpha, \mathrm{dom}(a))$ from $s_0$:
$\mathrm{output}(\mathrm{run}(s_0, \alpha), a) =
\mathrm{output}(\mathrm{run}(s_0, \mathrm{purge}(\alpha, \mathrm{dom}(a))), a)$.

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, Definition 2.
