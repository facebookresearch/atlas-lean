# Church–Rosser property of System T

Write $\to_T$ for [one-step full reduction](system-t-full-reduction/step.md) of System T (β-reduction together with the recursor rules, in any context), $\to_T^*$ for [multi-step reduction](system-t-full-reduction/steps.md), $=_T$ for the convertibility it generates, and $\underline{n} = \mathrm{S}^n\,0$ for the numerals. The reduction $\to_T$ is confluent: if $M \to_T^* N_1$ and $M \to_T^* N_2$, then $N_1 \to_T^* P$ and $N_2 \to_T^* P$ for some term $P$. Consequently a term has at
most one normal form, and two terms are convertible exactly when they have a common reduct.

## Depends on

- [Gödel's System T](godel-s-system-t.md)
- [Full reduction of System T](system-t-full-reduction/step.md)
- [Multi-step reduction of System T](system-t-full-reduction/steps.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definition 11.6.1 (System T) and Theorem 11.6.3, proved by the Tait–Martin-Löf parallel-reduction technique.
