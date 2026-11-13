# CPA advantage

Let $K$, $X$ and $R$ be nonempty finite sets, $Y$ an additive commutative
group, $q$ a natural number, $F \colon K \to X \to Y$ a keyed function and $A$ a CPA adversary
with coins in $R$. The CPA advantage of $A$ is the real number $|p - 1/2|$, where $p$ is the
probability that the CPA experiment for $F$ and $A$ with at most $q$ encryption queries outputs
true, that is, that $A$ guesses the challenge bit.
