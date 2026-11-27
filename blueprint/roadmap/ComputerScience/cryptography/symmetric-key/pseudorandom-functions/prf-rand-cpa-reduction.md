# The CPA reduction against a random function

Let $X$ be a finite nonempty set, $Y$ a
finite additive commutative group, $q$ a natural number and $A$ a CPA adversary with coins in a
finite nonempty set. Let $p$ be the probability that the CPA reduction built from $A$ (whose
encryption oracle answers at most $q$ queries) outputs $1$, that is, that $A$ guesses the
challenge bit, when its oracle is a uniformly random function $X \to Y$ and its coins are
uniform. Then $|p - 1/2| \le q / (2|X|)$.

The success probability is exactly $1/2$ unless the challenge randomness repeats the randomness
of one of the at most $q$ encryption queries.
