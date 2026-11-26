# Dummy sufficiency for one exchange

A protocol $\pi$ emulates $\phi$ if and only if there is one intermediary program $D$ such that,
for every environment $E$, the final-bit ensembles `exec π E dummy` and `exec φ E D` are close.
The real execution uses the two-way forwarder; the comparison execution uses its simulator $D$,
chosen before $E$ and independently of the parameter $k$ and auxiliary input $z$. Closeness is
negligible bit advantage as $k$ grows, uniformly over $z$ for each fixed $E$.

To simulate any other intermediary $A$, the enlarged environment runs $A$ internally and the
simulator for $A$ composes it with $D$. Both are programs of the same uniform polynomial-clock
language. This equivalence is qualitative; the extra gates need not preserve numerical overhead
or slack.

## Sources

- fixed-schedule instance of the reduction in R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC Summer School (2025), slides 50–53.
