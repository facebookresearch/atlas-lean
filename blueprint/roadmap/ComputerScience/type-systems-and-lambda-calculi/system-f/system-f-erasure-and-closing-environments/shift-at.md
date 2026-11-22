# Shift of untyped bound indices above a cutoff

For a cutoff $c \in \mathbb{N}$, the shift $\uparrow_c t$ of an untyped term $t$ (among the untyped λ-terms (locally nameless, with free variables named by natural numbers and bound variables given by de Bruijn indices)) adds one to every bound index $i \ge c$ and leaves the indices $i < c$ and the free variables unchanged; it commutes with application, and $\uparrow_c (\lambda.b) = \lambda.\uparrow_{c+1} b$.
