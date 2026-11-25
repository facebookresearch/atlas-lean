# Lifting free de Bruijn indices of a π-calculus process

For a cutoff $k \in \mathbb{N}$, the lifting $\uparrow_k P$ of a [process](proc.md) $P$ applies the [lifting of names](lift-name.md) above $k$ to every name of $P$, with the cutoff increased by one under each binder: $\uparrow_k \mathbf{0} = \mathbf{0}$, $\uparrow_k (\bar{a}\langle b\rangle.P) = \overline{\uparrow_k a}\langle \uparrow_k b\rangle.\uparrow_k P$, $\uparrow_k (a(\cdot).P) = (\uparrow_k a)(\cdot).\uparrow_{k+1} P$, $\uparrow_k (\nu P) = \nu \uparrow_{k+1} P$, and $\uparrow_k$ commutes with $\mid$, $!$ and $+$.
