# Table invariant of the simulation

A table of encryption answers satisfies the invariant for keys $(k_1, k_2)$ when every entry
$((c, t), m)$ has a valid tag $t = F(k_2, c)$ and decrypts correctly, $\mathrm{Dec}_{k_1}(c) = m$.
