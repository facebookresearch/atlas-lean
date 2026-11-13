# Generating function of the binomial transform over a field

Let $K$ be a field and let
$a : \mathbb{N} \to K$ be a sequence with ordinary generating function
$A(X) = \sum_n a_n X^n \in K[[X]]$. Then the ordinary generating function of the binomial
transform $n \mapsto \sum_{k=0}^{n} \binom{n}{k} a_k$ of $a$ equals
$(1 - X)^{-1} \cdot A\big(X (1 - X)^{-1}\big)$ in $K[[X]]$, where $A\big(X (1 - X)^{-1}\big)$ is
the power series obtained by substituting $X (1 - X)^{-1}$ for $X$ in $A$.
