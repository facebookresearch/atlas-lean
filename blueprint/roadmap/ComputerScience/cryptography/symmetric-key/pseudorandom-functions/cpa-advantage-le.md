# CPA encryption from a PRF, concrete security

Let $K$, $X$ and $R$ be nonempty finite sets,
$Y$ a finite additive commutative group, $q$ a natural number and $F \colon K \to X \to Y$ a keyed
function, used in the scheme $\mathrm{Enc}_k(m) = (r, F_k(r) + m)$ with uniform randomness
$r \in X$. For every CPA adversary $A$ with coins in $R$, the CPA advantage of $A$ in the
experiment whose encryption oracle answers at most $q$ queries is at most the PRF advantage of $F$
against the distinguisher built from $A$ plus $q / (2 |X|)$.

This is the reduction of Katz and Lindell, Theorem 3.31, with the sharper statistical term
$q / (2 |X|)$ in place of $q / |X|$.
