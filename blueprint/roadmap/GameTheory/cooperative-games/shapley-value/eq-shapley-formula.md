# The Shapley value is given by Shapley's formula

On a fixed finite set $N$ of $n$ players, every linear value $\varphi$ that is efficient,
symmetric and gives nothing to null players pays player $i$

$$\varphi_i(v) = \sum_{S \ni i} \frac{(|S| - 1)!\,(n - |S|)!}{n!}\,\bigl(v(S) - v(S \setminus \{i\})\bigr).$$

Shapley's formula satisfies the three axioms, and by
[uniqueness](shapley-characterization.md) it is the only value that does. Compared with the
statement in the source, the axioms are those of the adapted fixed-player-set characterisation
(linearity in place of additivity), so the hypotheses are slightly stronger than Shapley's; the
conclusion, the formula, is the same.

## Informally uses

- [Existence and uniqueness of the Shapley value](shapley-characterization.md): uniqueness.
- [Shapley's formula is efficient](shapley-formula-is-efficient.md),
  [Shapley's formula is symmetric](shapley-formula-is-symmetric.md) and
  [Shapley's formula gives nothing to null players](shapley-formula-satisfies-null-player-ax.md):
  the formula satisfies the axioms.

## Sources

- L. S. Shapley, "A value for n-person games", in Contributions to the Theory of Games II, Ann. of Math. Stud. 28, Princeton Univ. Press (1953), 307–317 (not read; attributed by the secondary source below).
- R. Serrano, "Cooperative games: core and Shapley value", CEMFI Working Paper 0709 (2007), §4.1, Theorem (Shapley, 1953) (secondary source).
