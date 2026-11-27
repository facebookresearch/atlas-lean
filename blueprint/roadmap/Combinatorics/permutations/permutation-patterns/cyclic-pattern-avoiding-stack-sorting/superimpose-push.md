# Push order of the superimpose operation

For finite sequences $a$ and $b$ of natural
numbers, $\mathrm{push}(a, b)$ is the sequence obtained by taking the first entry of $b$, then the
next two entries of $a$ (only one if just one is left), and repeating; once one of the two
sequences is exhausted, the remaining entries of the other follow in order.

For finite sequences $\sigma_1$ and $\sigma_2$ with reversals $\mathrm{rev}\,\sigma_1$ and
$\mathrm{rev}\,\sigma_2$, the sequence $\mathrm{push}(\mathrm{rev}\,\sigma_1,
\mathrm{rev}\,\sigma_2)$ is the order in which the superimpose operation
$\mathrm{si}(\sigma_1, \sigma_2)$ pushes the entries of $\sigma_1$ and $\sigma_2$ onto its stack.

## Sources

- Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026), Article A15, Section 3.2.
