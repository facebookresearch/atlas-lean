# HMMER Plan 7 restrictions

A [profile HMM](profile-hmm.md) satisfies the Plan 7 restrictions (Eddy 1998) if, for all nodes $k$ and types $s$,

- $t_k(D, I) = 0$ and $t_k(I, D) = 0$;
- $t_0(s, I) = 0$ and $t_L(s, I) = 0$: no insert states at the begin node and at the last node.

## Sources

- S. R. Eddy, *Profile hidden Markov models*, Bioinformatics 14 (1998), 755–763.
