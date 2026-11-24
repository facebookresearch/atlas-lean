# Running on presampled coins

Let $O : X \times R \to Y$ answer a query $x$ with coins $\rho$ by $O(x, \rho)$. Run on a list of coins,
an oracle computation has its $i$-th query answered with the $i$-th coin of the list, and with a
fixed default coin once the list is used up. A reduction that answers its adversary's encryption
queries itself does this (Katz and Lindell, proof of Proposition 11.3).
