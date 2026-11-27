# Asymptotic PRG security from a PRF

Let $K_n$, $X_n$, $Y_n$ and $R_n$ be families of finite
sets with $K_n$, $Y_n$ and $R_n$ nonempty, let $F_n : K_n \to X_n \to Y_n$ be a family of keyed
functions, and for each $n$ let $x_{n,1}, \dots, x_{n,\ell(n)} \in X_n$ be distinct points with
$|K_n| < |Y_n|^{\ell(n)}$. Let $G_n(k) = (F_n(k, x_{n,1}), \dots, F_n(k, x_{n,\ell(n)}))$. Take a
class of admissible distinguisher families for $G$, with coins in $R_n$, each of which draws its
coins uniformly from $R_n$, and a class of admissible PRF distinguisher families for $F$, with coins
in $R_n$, that contains, for every admissible family $A$, the family of PRF distinguishers built
from $A_n$ (query $x_{n,1}, \dots, x_{n,\ell(n)}$ and output the guess of $A_n$ on the answers). If
$F$ is a secure PRF relative to that class, then $G$ is a secure PRG relative to the admissible
distinguisher families: it expands, and every admissible family has negligible PRG advantage.

This is the asymptotic form of Boneh and Shoup, Theorem 4.8. The condition
$|K_n| < |Y_n|^{\ell(n)}$ is used only for expansion. It comes from the asymptotic PRG security
`PRGSecure`, which requires expansion, following Katz and Lindell; Boneh and Shoup's
Theorem 4.8 has no such hypothesis, and their Definition 3.1 of a secure PRG does not require
expansion. The efficiency of $F$, of $G$ and of the distinguishers is not modelled; any
restriction on the distinguishers is what the two classes encode.
