# Empirical grouped censored data

Let $Z_i = (T_i, C_i)$, for $i = 0, 1, 2, \dots$, be random pairs of an event time and a censoring time
in the grid $\{0, 1, \dots, k - 1\}$. For each $n$ and each outcome $\omega$, the empirical data are the
grouped right-censored data of the first $n$ subjects at the grid times $0, 1, \dots, k - 1$: subject $i$
is recorded at $\min(T_i, C_i)$, with an event when $T_i \le C_i$ and censored otherwise.
