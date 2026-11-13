# Neto's identity for higher-order Bernoulli numbers

For every complex number $x$ and all
natural numbers $n$ and $\ell$,

$$\sum_{k=0}^{n} \binom{n}{k} x^{n-k} B_{\ell+k}^{(x)} =
(-1)^{n+\ell} \sum_{k=0}^{\ell} \binom{\ell}{k} x^{\ell-k} B_{n+k}^{(x)},$$

where $B_m^{(x)}$ is the higher-order Bernoulli number of order $x$.

Proof: The substitution coefficient formula makes both sides polynomial in the order. For natural
orders, the cited Bernoulli EGF gives the reflection identity, formal differentiation proves Neto's
formula, and equality on all natural complex points finishes the polynomial argument.

## Sources

- https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex, lines 662-670.
