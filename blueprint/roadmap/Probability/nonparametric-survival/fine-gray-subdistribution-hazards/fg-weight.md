# Fine–Gray censoring weight

Given a censoring survival function $G$, the Fine–Gray weight of subject $l$ at the time $X_i$ of a cause-$c$ failure is $1$ if $X_l \ge X_i$, $G(X_i)/G(X_l)$ if $l$ failed before $X_i$ from another cause, and $0$ otherwise. The quotient is $0$ when $G(X_l) = 0$ ($x/0 = 0$).

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509.
