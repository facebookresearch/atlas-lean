# Sample-based distribution testers

Let $\Omega$ be a finite set with $|\Omega| = n$ and let $q$ be a fixed distribution on $\Omega$. A *$k$-sample tester for identity to $q$ with proximity $\varepsilon$* is a (possibly randomized) map from $\Omega^k$ to $\{\text{accept}, \text{reject}\}$ such that, given $k$ independent samples from an unknown distribution $p$, it accepts with probability at least $2/3$ if $p = q$ and rejects with probability at least $2/3$ if the total variation distance $d_{TV}(p, q) \ge \varepsilon$. *Uniformity testing* is the case $q$ uniform. A *closeness tester* receives $k$ samples from each of two unknown distributions $p, q$ and distinguishes $p = q$ from $d_{TV}(p, q) \ge \varepsilon$.

## Sources

- C. L. Canonne, "A Survey on Distribution Testing: Your Data is Big. But is it Blue?", Theory of Computing Graduate Surveys 9, 2020.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
