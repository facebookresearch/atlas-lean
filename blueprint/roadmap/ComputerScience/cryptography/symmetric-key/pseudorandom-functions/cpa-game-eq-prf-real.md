# The CPA reduction is exact with the real oracle

Let $K$, $X$ and $R$ be nonempty finite
sets, $Y$ an additive commutative group, $q$ a natural number and $F \colon K \to X \to Y$ a keyed
function. For every CPA adversary $A$ with coins in $R$, the CPA experiment for $F$ and $A$ with
at most $q$ encryption queries has the same output distribution as the real world of the PRF
experiment for $F$ run with the distinguisher built from $A$ for $q$ queries: with the oracle $F_k$
for a uniform key $k$, the reduction runs the CPA experiment exactly.
