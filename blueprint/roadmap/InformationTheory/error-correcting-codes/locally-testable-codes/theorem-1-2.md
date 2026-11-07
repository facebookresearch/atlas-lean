# Good locally testable codes of every rate below one

For every real number $\rho$ with
$0 \le \rho < 1$ there exist a natural number $q$, a real number $\kappa > 0$, lengths
$n_i \in \mathbb{N}$ and binary codes $C_i$ of length $n_i$ for $i \in \mathbb{N}$ such that the
family $(C_i)_{i \in \mathbb{N}}$ is good and, for every $i$, the code $C_i$ is $\kappa$-locally
testable with $q$ queries and has rate at least $\rho$.

The source's theorem also asserts that the codes are explicit; explicitness is not formalized.

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, and S. Mozes, `Good Locally Testable Codes`, Annals of Math, 203 (2) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-2-GoodLTCodes.lean Via leanprover/lean-eval@38361be, problem `annals_good_lt_codes`.
