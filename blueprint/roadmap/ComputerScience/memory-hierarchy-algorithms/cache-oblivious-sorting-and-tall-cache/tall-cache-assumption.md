# Tall-cache assumptions

In the $(Z, L)$ ideal-cache model, a *tall-cache assumption of strength $\varepsilon > 0$* is the hypothesis $Z \ge c\, L^{1+\varepsilon}$ for a constant $c > 0$, i.e. the cache holds at least $c\,L^{\varepsilon}$ lines. The *standard tall-cache assumption* is the case $\varepsilon = 1$, $Z = \Omega(L^2)$. A cache-oblivious algorithm is analyzed for all $Z, L$ satisfying the assumption simultaneously, without knowing them.

## Depends on

- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Sources

- Matteo Frigo, Charles E. Leiserson, Harald Prokop, Sridhar Ramachandran, "Cache-Oblivious Algorithms", FOCS (1999); ACM Transactions on Algorithms 8(1) (2012).
- Gerth Stølting Brodal, Rolf Fagerberg, "On the Limits of Cache-Obliviousness", STOC (2003).
