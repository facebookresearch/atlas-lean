# Encrypt-then-authenticate

Given a private-key encryption scheme and a message authentication code on its ciphertexts, the
encrypt-then-authenticate scheme (Katz and Lindell, Section 4.5) uses independent keys $k_1$ and
$k_2$. It encrypts $m$ as $(c, t)$, where $c \leftarrow \mathrm{Enc}_{k_1}(m)$ and
$t \leftarrow \mathrm{Mac}_{k_2}(c)$, and it decrypts $(c, t)$ to $\bot$ unless
$\mathrm{Vrfy}_{k_2}(c, t) = 1$, and otherwise to $\mathrm{Dec}_{k_1}(c)$.
