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

- Redha Chellal, Farid Bencherif, and Mohamed Mehbali, *An Identity for Generalized Bernoulli Polynomials*, Journal of Integer Sequences 23 (2020), Article 20.11.2, Section 5.8 (Neto's identity), equation (59), <https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.html>; originally A. F. Neto, *Carlitz's identity for the Bernoulli numbers and Zeon algebra*, Journal of Integer Sequences 18 (2015), Article 15.5.6.
