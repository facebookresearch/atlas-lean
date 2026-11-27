# Asymptotic security

Let $\mathrm{adv}_n(A)$ be the advantage of an adversary $A$ at security parameter $n$, and fix a
class of admissible adversary families, each giving one adversary $A_n$ for every $n$. Security
holds asymptotically when every admissible family has negligible advantage
$n \mapsto \mathrm{adv}_n(A_n)$. This is the shape of Katz and Lindell's Definitions 3.8, 3.22, 4.2,
11.2 and 12.2, whose admissible families are the probabilistic polynomial-time ones. The statement
holds vacuously when no family is admissible, for instance when at some security parameter there
are no adversaries at all.
