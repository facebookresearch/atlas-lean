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

- https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex Identity span: lines 662-670, text_sha256 `06790ccab662e77ae848bda8ff92dac6a404d8b43042d433d80c6dd7b127c56f`. File sha256 `ce83119262833b8219cb7670521e7602617dae3f645a76e913bff79b7ba7dc9c`.
