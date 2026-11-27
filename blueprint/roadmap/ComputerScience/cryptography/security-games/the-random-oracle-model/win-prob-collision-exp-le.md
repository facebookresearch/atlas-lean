# The collision bound in the random-oracle model

Let the domain `D` have decidable equality and the range `Rng` be finite and
nonempty. If the query points `xs : Fin q → D` are pairwise distinct, the
probability that two of the random oracle's answers coincide is at most `q (q
- 1) / (2 |Rng|)`. This slightly strengthens, and implies, Katz and Lindell's
Lemma A.15, which states the bound `q ^ 2 / (2 |Rng|)`.
