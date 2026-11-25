# Ordinary generating function of the binomial transform

Let $a : \mathbb{N} \to \mathbb{R}$
be a real sequence with ordinary generating function $A(X) = \sum_n a_n X^n \in \mathbb{R}[[X]]$.
Then the ordinary generating function of the binomial transform
$n \mapsto \sum_{k=0}^{n} \binom{n}{k} a_k$ of $a$ equals
$(1 - X)^{-1} \cdot A\big(X (1 - X)^{-1}\big)$ in $\mathbb{R}[[X]]$, where
$A\big(X (1 - X)^{-1}\big)$ is the power series obtained by substituting $X (1 - X)^{-1}$ for $X$
in $A$.

## Sources

- Ayhan Dil, Veli Kurt, and Mehmet Cenkci, "Algorithms for Bernoulli and Related Polynomials," Journal of Integer Sequences 10 (2007), Article 07.5.4, Proposition 1.1, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.pdf>.
