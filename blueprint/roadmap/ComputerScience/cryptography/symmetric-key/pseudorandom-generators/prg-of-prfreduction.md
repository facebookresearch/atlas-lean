# The PRF distinguisher built from a PRG distinguisher

Let $x_1, \dots, x_n \in X$ and let
$A$ be a distinguisher for strings in $Y^n$ with coins in $R$. With coins $r \in R$ and with oracle
access to a function $O : X \to Y$, the distinguisher queries $O$ at $x_1, \dots, x_n$, in this
order, and outputs the guess of $A$ on $(O(x_1), \dots, O(x_n))$ with coins $r$.
