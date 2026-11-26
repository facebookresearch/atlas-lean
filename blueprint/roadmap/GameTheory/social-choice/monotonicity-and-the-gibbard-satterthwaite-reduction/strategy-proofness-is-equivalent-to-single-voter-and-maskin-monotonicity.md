# Strategy-proofness is equivalent to single-voter and Maskin monotonicity

A social choice function on strict rankings is strategy-proof if and only if it is single-voter monotone. With finitely many voters, these conditions are also equivalent to Maskin monotonicity.

## Proof sketch

If a change of one ranking moves the outcome from $a$ to $a'$, strategy-proofness for the voter with ranking $P_i$ (resp. $Q_i$) forbids preferring $a'$ (resp. $a$). For Maskin monotonicity, change voters' rankings one at a time and apply single-voter monotonicity at each step.

## Depends on

- [Maskin monotonicity and single-voter monotonicity](maskin-monotonicity-and-single-voter-monotonicity.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
- Eitan Muller and Mark A. Satterthwaite, "The Equivalence of Strong Positive Association and Strategy-Proofness", Journal of Economic Theory, 1977.
