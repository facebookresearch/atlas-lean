# The MAC from a PRF, concrete security

Let $K$, $M$, $T$ and $R$ be finite types with
$K$, $T$ and $R$ nonempty, let $F \colon K \to M \to T$ be a keyed function, and let $A$ be an
adaptive chosen-message forger: for coins $r \in R$, $A(r)$ is an adaptive oracle algorithm
with queries in $M$, answers in $T$ and output in $M \times T$. Then the probability that $A$
wins the existential-forgery experiment for the MAC $\mathrm{Mac}_k(m) = F(k, m)$ is at most
the PRF advantage against $F$ of the distinguisher that, on coins $r$, runs the MAC reduction
on $A(r)$ starting from the empty query log, plus $1 / |T|$.

This is the reduction of Katz and Lindell, Theorem 4.6, stated as a concrete inequality.
