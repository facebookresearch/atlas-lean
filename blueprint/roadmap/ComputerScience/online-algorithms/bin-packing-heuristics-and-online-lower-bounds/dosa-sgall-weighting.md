# The Dósa-Sgall weighting for First Fit

Give an item of size $a$ (capacity $C$) the weight $\frac{6}{5}\frac{a}{C}$ plus a **bonus** equal to $0.4$ if $a > C/2$, $0.1$ if $C/3 \le a \le C/2$, $\frac35\big(\frac{a}{C} - \frac16\big)$ if $C/6 < a < C/3$, and $0$ otherwise. Then every bin of total size at most $C$ has total weight at most $1.7$, while the items of any instance that First Fit packs into $FF$ bins have total weight at least $FF - 3$ (Dósa and Sgall, Section 1.2).

## Proof sketch

The upper bound is a case analysis on the number of large and medium items in a bin. For the lower bound, amortize over First Fit bins: a bin whose items are small is nearly full because later items did not fit, and bonuses of large items pay for under-filled bins.

## Depends on

- [Next Fit and First Fit](next-fit-and-first-fit.md)

## Sources

- G. Dósa and J. Sgall, "First Fit Bin Packing: A Tight Analysis", 30th International Symposium on Theoretical Aspects of Computer Science (STACS), 2013.
