# Reducing before the $123$ cyclic sorting machine does not change the reduced output

For
every permutation $\pi$ of $[n] = \{1, \ldots, n\}$, applying the cyclic sorting machine
$\mathrm{SC}_{[123]}$ to the reduction $\operatorname{red}(\pi)$ and reducing the result gives the
reduction of $\mathrm{SC}_{[123]}(\pi)$:
$\operatorname{red}(\mathrm{SC}_{[123]}(\operatorname{red}(\pi))) =
\operatorname{red}(\mathrm{SC}_{[123]}(\pi))$.

Only this identity is stated; the lemma's further assertion that blocks $a, a+1, \ldots, a+k$ of
$\pi$ enter and leave the stack together is not part of the statement.

## Sources

- Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026), Article A15, Lemma 1.
