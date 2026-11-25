# Decryption of encrypt-then-authenticate

The encrypt-then-authenticate scheme decrypts $(c, t)$ under $(k_1, k_2)$ to $\mathrm{Dec}_{k_1}(c)$
if $\mathrm{Vrfy}_{k_2}(c, t) = 1$, and to $\bot$ otherwise.
