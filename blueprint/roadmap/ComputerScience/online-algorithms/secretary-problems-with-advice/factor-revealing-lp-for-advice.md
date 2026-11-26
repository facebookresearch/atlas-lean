# A unified factor-revealing LP for secretaries with advice

For every advice model in which the signals are exchangeable with the arrival order and conditionally independent across candidates given their qualities, the optimal win probability equals the value of a linear program generalizing the secretary LP, with one variable for each position and each possible (relative rank, signal) pair. Solving its dual gives tight analyses and optimal policies for secretaries with samples, for qualities drawn from a known distribution (the full-information secretary problem, with optimal win probability approximately $0.5801$), and for a noisy binary advice model.

## Proof sketch

Exchangeability makes the event "the current candidate is best so far with signal $s$" have a probability depending only on the position and $s$, independent of the past behavior of the policy, so the stopping constraints are linear exactly as in the classical case. Optimal dual solutions certify optimality of explicit threshold policies; for the full-information case the LP limit reproduces Gilbert and Mosteller's constant.

## Depends on

- [Linear-programming characterization of the classical secretary problem](secretary-lp.md)

## Proof depends on

- [Linear-programming characterization of the classical secretary problem](secretary-lp.md)

## Sources

- Paul Dütting, Silvio Lattanzi, Renato Paes Leme, Sergei Vassilvitskii, "Secretaries with Advice", EC (2021); Mathematics of Operations Research 49(2) (2024), arXiv:2011.06726.
