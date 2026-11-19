# Evaluation of terms

Given an environment $e : \mathbb{N} \to \mathbb{R}$, the value of a
term in $\mathbb{R}$ is defined by recursion on the term: the variable with de Bruijn index $i$ has
value $e(i)$, the integer constant $k$ has value $k$, and the value of a sum, product or negation
of terms is the sum, product or negation in $\mathbb{R}$ of the values of its parts.
