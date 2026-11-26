# Tseitin correctness

Let $\iota$ be an injective map from atoms to natural numbers, let
$A$ be a proposition and let $v$ be a valuation of the atoms. Then $A$ is true under $v$ if and
only if some assignment $\sigma : \mathbb{N} \to \mathrm{Bool}$ with $\sigma(2\iota(a)) = v(a)$
for every atom $a$ satisfies the Tseitin CNF of $A$ with respect to $\iota$.
