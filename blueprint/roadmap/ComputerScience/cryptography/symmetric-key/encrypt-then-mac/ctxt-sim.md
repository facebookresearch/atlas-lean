# The MAC forger's simulation of a ciphertext forger

Given a key $k_1$ and a tape $(r_1, r_2, \dots)$, the simulation runs a ciphertext forger against
encrypt-then-MAC. It answers the $i$-th encryption query $m$ by computing $c = E(k_1, m, r_i)$, with
a fixed default entry in place of $r_i$ once the tape is used up, asking its own MAC oracle for the
tag $t$ of $c$, and returning $(c, t)$. Its output is the ciphertext the forger outputs.
